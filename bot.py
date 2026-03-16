import os
from dotenv import load_dotenv

load_dotenv()

import csv
import aiohttp
import asyncio
import zipfile
import logging
import hashlib
import base64
import asyncpg
import tempfile
import re
import io
import fitz  # PyMuPDF
from dataclasses import dataclass, field
from collections import Counter
from statistics import median
from datetime import datetime, timedelta
from zoneinfo import ZoneInfo

from telegram import (
    Update,
    ReplyKeyboardMarkup,
    KeyboardButton,
    InlineKeyboardMarkup,
    InlineKeyboardButton,
)
from telegram.ext import (
    Application,
    CommandHandler,
    MessageHandler,
    CallbackQueryHandler,
    filters,
    ContextTypes,
)
from aiohttp import web

# =========================
# Настройка логов
# =========================
logging.basicConfig(
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    level=logging.INFO
)
logger = logging.getLogger(__name__)

# =========================
# Константы/настройки
# =========================
TZ = ZoneInfo("Asia/Tbilisi")

MODE_CARDS = "cards"
MODE_RECEIPTS = "receipts"

BTN_CARDS = "💳 Проверка карт"
BTN_CARDS_ACTIVE = "✅ Проверка карт"
BTN_RECEIPTS = "🧾 Проверка чеков"
BTN_RECEIPTS_ACTIVE = "✅ Проверка чеков"
BTN_INVITE = "👥 Пригласить"
BTN_ACCESS = "⭐ Доступ"
BTN_ADMIN_PANEL = "🛠 Админка"
BTN_ADMIN_GRANT_30D = "♾️ Выдать безлимит на 30 дней"
BTN_ADMIN_STATS = "📊 Статистика"
BTN_ADMIN_BROADCAST = "📣 Рассылка"
BTN_ADMIN_BACK = "🏠 В меню"

MAX_PDF_SIZE_MB = 15
INITIAL_RECEIPT_QUOTA = 3
REFERRAL_REWARD_AMOUNT = 10
UNLIMITED_PLAN_DAYS = 30
UNLIMITED_PRICE_USDT = "5"


def parse_admin_ids() -> set[int]:
    raw = (os.getenv("ADMIN_IDS", "") or "").strip()
    if raw:
        parts = [p.strip() for p in raw.replace(";", ",").split(",")]
        ids = {int(p) for p in parts if p.isdigit() and int(p) != 0}
        return ids

    one = (os.getenv("ADMIN_ID", "0") or "0").strip()
    return {int(one)} if one.isdigit() and int(one) != 0 else set()


ADMIN_IDS = parse_admin_ids()

CARD_HASH_SALT = os.getenv("CARD_HASH_SALT", "")

DATABASE_URL = os.getenv("DATABASE_URL", "")
WEBHOOK_URL = os.getenv("WEBHOOK_URL", "")
WEBHOOK_SECRET = os.getenv("WEBHOOK_SECRET", "")

# =========================
# Поддержка / FAQ / Политика / Соцсети
# =========================
SUPPORT_USERNAME = "@cashoutta1"
NEWS_CHANNEL_URL = "https://t.me/bincheker_news"
PRIVACY_URL = "https://telegra.ph/Politika-konfidencialnosti---card-bin-checkerbot-03-16"
FAQ_URL = "https://telegra.ph/FAQ---card-bin-checkerbot-03-16"

SUPPORT_KB = InlineKeyboardMarkup([
    [InlineKeyboardButton("✉️ Контакты (сотрудничество)", url=f"https://t.me/{SUPPORT_USERNAME.lstrip('@')}")],
    [InlineKeyboardButton("💎 Новости и обновления", url=NEWS_CHANNEL_URL)],
    [InlineKeyboardButton("📗 F.A.Q", url=FAQ_URL)],
    [InlineKeyboardButton("📝 Условия пользования", url=PRIVACY_URL)],
])

# =========================
# Глобальные переменные
# =========================
bin_db: dict[str, tuple[str, str, str]] = {}

_db_pool: asyncpg.Pool | None = None
_db_lock = asyncio.Lock()

_http_session: aiohttp.ClientSession | None = None

_rapira_cache = {"ts": 0.0, "data": None}
_RAPIRA_CACHE_SECONDS = 30

_binlist_cache: dict[str, tuple[float, dict]] = {}
_BINLIST_CACHE_SECONDS = 3600

_bot_username_cache: str | None = None
_bot_username_lock = asyncio.Lock()

# =========================
# Utils
# =========================
def today_str() -> str:
    return datetime.now(TZ).strftime("%Y-%m-%d")


def now_iso() -> str:
    return datetime.now(TZ).isoformat(timespec="seconds")


def monotonic_now() -> float:
    return asyncio.get_running_loop().time()


def safe_str(value) -> str:
    return str(value).strip() if value is not None else ""


def is_admin_user(update: Update) -> bool:
    u = update.effective_user
    return bool(u and u.id in ADMIN_IDS)


def get_mode(context: ContextTypes.DEFAULT_TYPE) -> str:
    return context.user_data.get("mode", MODE_CARDS)


def set_mode(context: ContextTypes.DEFAULT_TYPE, mode: str):
    context.user_data["mode"] = mode


def is_cards_button(text: str) -> bool:
    return text in {BTN_CARDS, BTN_CARDS_ACTIVE}


def is_receipts_button(text: str) -> bool:
    return text in {BTN_RECEIPTS, BTN_RECEIPTS_ACTIVE}


def build_menu(is_admin: bool, mode: str) -> ReplyKeyboardMarkup:
    cards_btn = BTN_CARDS_ACTIVE if mode == MODE_CARDS else BTN_CARDS
    receipts_btn = BTN_RECEIPTS_ACTIVE if mode == MODE_RECEIPTS else BTN_RECEIPTS

    rows = [
        [KeyboardButton(cards_btn), KeyboardButton(receipts_btn)],
        [KeyboardButton("📚 Помощь"), KeyboardButton("📈 Курс Rapira")],
        [KeyboardButton(BTN_INVITE), KeyboardButton(BTN_ACCESS)],
    ]
    if is_admin:
        rows.append([KeyboardButton(BTN_ADMIN_PANEL)])
    return ReplyKeyboardMarkup(rows, resize_keyboard=True)


def build_admin_menu() -> ReplyKeyboardMarkup:
    rows = [
        [KeyboardButton(BTN_ADMIN_GRANT_30D)],
        [KeyboardButton(BTN_ADMIN_STATS), KeyboardButton(BTN_ADMIN_BROADCAST)],
        [KeyboardButton(BTN_ADMIN_BACK)],
    ]
    return ReplyKeyboardMarkup(rows, resize_keyboard=True)


def get_support_text(mode: str) -> str:
    mode_hint = (
        "💳 <b>Текущий режим</b>: Проверка карт\n"
        "Отправь 6 цифр BIN или полный номер карты.\n\n"
        "🧾 Для проверки PDF-чека переключись на режим <b>Проверка чеков</b>."
        if mode == MODE_CARDS
        else
        "🧾 <b>Текущий режим</b>: Проверка чеков\n"
        "Отправь PDF-файл чека.\n\n"
        "💳 Для проверки BIN/карты переключись на режим <b>Проверка карт</b>."
    )

    return (
        "📚 <b>Помощь</b>\n\n"
        "💳 <b>Проверка карт</b> — доступна всегда.\n"
        "🧾 <b>Проверка чеков</b> — по доступам.\n"
        f"🎁 За 1 подтверждённого пользователя начисляется +{REFERRAL_REWARD_AMOUNT}.\n"
        "ℹ️ Подтверждённый пользователь — тот, кто пришёл по ссылке и выполнил действие: "
        "проверил карту или чек.\n"
        f"♾️ Можно активировать безлимит на {UNLIMITED_PLAN_DAYS} дней за {UNLIMITED_PRICE_USDT} USDT.\n\n"
        f"{mode_hint}\n\n"
        f"✉️ <b>Контакты</b>:\n{SUPPORT_USERNAME} | Cотрудничество\n\n"
        "💎 <b>Социальные сети</b>:\n"
        "BIN Чекер | Новости и Обновления\n"
        f"{NEWS_CHANNEL_URL}\n\n"
        "📝 <b>Условия пользования</b>:\n"
        f"{PRIVACY_URL}\n\n"
        "📗 <b>F.A.Q</b>:\n"
        f"{FAQ_URL}"
    )


def fire_and_forget(task: asyncio.Task):
    def _done(t: asyncio.Task):
        try:
            t.result()
        except Exception as e:
            logger.error(f"Background task error: {e}")

    task.add_done_callback(_done)


# =========================
# HTTP session
# =========================
async def get_http_session() -> aiohttp.ClientSession:
    global _http_session
    if _http_session is None or _http_session.closed:
        timeout = aiohttp.ClientTimeout(
            total=8,
            connect=2,
            sock_connect=2,
            sock_read=5,
        )
        connector = aiohttp.TCPConnector(
            limit=100,
            limit_per_host=20,
            ttl_dns_cache=300,
            enable_cleanup_closed=True,
        )
        _http_session = aiohttp.ClientSession(timeout=timeout, connector=connector)
    return _http_session


# =========================
# DB helpers
# =========================
async def _db_connect():
    global _db_pool
    if _db_pool is None:
        if not DATABASE_URL:
            raise RuntimeError("DATABASE_URL не задан. Добавь в .env и в Render Env.")
        _db_pool = await asyncpg.create_pool(
            DATABASE_URL,
            min_size=2,
            max_size=10,
            command_timeout=5,
        )


async def _db_init_schema():
    await _db_connect()
    assert _db_pool is not None
    async with _db_pool.acquire() as conn:
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS users (
                user_id     BIGINT PRIMARY KEY,
                username    TEXT,
                first_seen  TEXT,
                last_seen   TEXT,
                starts      INTEGER DEFAULT 0,
                requests    INTEGER DEFAULT 0
            );
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS daily (
                day          TEXT PRIMARY KEY,
                starts       INTEGER DEFAULT 0,
                requests     INTEGER DEFAULT 0,
                unique_users INTEGER DEFAULT 0
            );
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS user_day (
                user_id BIGINT,
                day     TEXT,
                PRIMARY KEY (user_id, day)
            );
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS pan_hash (
                h   TEXT PRIMARY KEY,
                cnt INTEGER DEFAULT 0
            );
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS pan_flags (
                h          TEXT PRIMARY KEY,
                is_problem INTEGER DEFAULT 0,
                flagged_at TEXT,
                flagged_by BIGINT
            );
        """)

        await conn.execute("ALTER TABLE users ADD COLUMN IF NOT EXISTS receipt_checks INTEGER DEFAULT 0;")
        await conn.execute("ALTER TABLE daily ADD COLUMN IF NOT EXISTS receipt_checks INTEGER DEFAULT 0;")
        await conn.execute(
            f"ALTER TABLE users ADD COLUMN IF NOT EXISTS receipt_quota INTEGER DEFAULT {INITIAL_RECEIPT_QUOTA} NOT NULL;"
        )
        await conn.execute("ALTER TABLE users ADD COLUMN IF NOT EXISTS invited_by BIGINT NULL;")
        await conn.execute("ALTER TABLE users ADD COLUMN IF NOT EXISTS referrals_total INTEGER DEFAULT 0 NOT NULL;")
        await conn.execute("ALTER TABLE users ADD COLUMN IF NOT EXISTS referral_reward_total INTEGER DEFAULT 0 NOT NULL;")
        # TODO: migrate unlimited_until to TIMESTAMPTZ in a dedicated safe migration.
        await conn.execute("ALTER TABLE users ADD COLUMN IF NOT EXISTS unlimited_until TEXT NULL;")
        await conn.execute("ALTER TABLE users ADD COLUMN IF NOT EXISTS paid_plan TEXT NULL;")
        await conn.execute("ALTER TABLE users ADD COLUMN IF NOT EXISTS paid_source TEXT NULL;")
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS referrals (
                invited_user_id BIGINT PRIMARY KEY,
                inviter_user_id BIGINT NOT NULL,
                created_at      TEXT NOT NULL,
                qualified_at    TEXT NULL,
                rewarded        INTEGER DEFAULT 0 NOT NULL,
                rewarded_at     TEXT NULL,
                reward_amount   INTEGER DEFAULT 10 NOT NULL
            );
        """)


async def db_init():
    async with _db_lock:
        await _db_init_schema()


async def db_execute(query: str, params=()):
    await _db_connect()
    assert _db_pool is not None
    async with _db_pool.acquire() as conn:
        await conn.execute(query, *params)


async def db_fetchone(query: str, params=()):
    await _db_connect()
    assert _db_pool is not None
    async with _db_pool.acquire() as conn:
        return await conn.fetchrow(query, *params)


async def db_fetchall(query: str, params=()):
    await _db_connect()
    assert _db_pool is not None
    async with _db_pool.acquire() as conn:
        return await conn.fetch(query, *params)


def normalize_username_input(text: str) -> str:
    value = safe_str(text).strip()
    if value.startswith("@"):
        value = value[1:]
    value = value.strip().lower()
    if not value:
        return ""
    if not re.fullmatch(r"[a-z0-9_]{5,32}", value):
        return ""
    return value


async def find_user_id_by_username(username: str) -> int | None:
    normalized = normalize_username_input(username)
    if not normalized:
        return None

    row = await db_fetchone(
        """
        SELECT user_id
        FROM users
        WHERE username IS NOT NULL
          AND lower(username) = $1
        ORDER BY last_seen DESC NULLS LAST
        LIMIT 1
        """,
        (normalized,)
    )
    return int(row["user_id"]) if row else None


async def ensure_daily_row(day: str):
    await db_execute(
        "INSERT INTO daily (day, starts, requests, unique_users, receipt_checks) VALUES ($1, 0, 0, 0, 0) "
        "ON CONFLICT (day) DO NOTHING",
        (day,)
    )


def _parse_iso_dt(value) -> datetime | None:
    if not value:
        return None
    if isinstance(value, datetime):
        return value
    try:
        return datetime.fromisoformat(value)
    except Exception:
        return None


def is_unlimited_active(unlimited_until) -> bool:
    dt = _parse_iso_dt(unlimited_until)
    if not dt:
        return False
    return dt > datetime.now(TZ)


def format_access_until(unlimited_until) -> str:
    dt = _parse_iso_dt(unlimited_until)
    if not dt:
        return "—"
    return dt.astimezone(TZ).strftime("%d.%m.%Y %H:%M")


def parse_start_referral(text: str | None) -> int | None:
    if not text:
        return None
    m = re.match(r"^/start(?:@\w+)?(?:\s+(.*))?$", text.strip())
    if not m:
        return None
    arg = (m.group(1) or "").strip()
    if not arg.startswith("ref_"):
        return None
    ref = arg[4:].strip()
    if not ref.isdigit():
        return None
    uid = int(ref)
    return uid if uid > 0 else None


async def get_personal_referral_link(bot, user_id: int) -> str:
    bot_username = await get_bot_username(bot)
    if not bot_username:
        return f"ref_{user_id}"
    return f"https://t.me/{bot_username}?start=ref_{user_id}"


async def get_bot_username(bot) -> str:
    global _bot_username_cache
    if _bot_username_cache is not None:
        return _bot_username_cache

    async with _bot_username_lock:
        if _bot_username_cache is not None:
            return _bot_username_cache
        bot_info = await bot.get_me()
        _bot_username_cache = bot_info.username or ""
        return _bot_username_cache


async def ensure_user_exists(user_id: int, username: str | None):
    await _db_connect()
    assert _db_pool is not None

    ts = now_iso()
    new_username = username if username else None

    async with _db_pool.acquire() as conn:
        await conn.execute(
            f"""
            INSERT INTO users (
                user_id, username, first_seen, last_seen, starts, requests, receipt_checks,
                receipt_quota, referrals_total, referral_reward_total
            )
            VALUES ($1, $2, $3, $3, 0, 0, 0, {INITIAL_RECEIPT_QUOTA}, 0, 0)
            ON CONFLICT (user_id) DO UPDATE SET
                username  = COALESCE(EXCLUDED.username, users.username),
                last_seen = EXCLUDED.last_seen
            """,
            user_id, new_username, ts
        )


async def bind_referral(invited_user_id: int, inviter_user_id: int) -> bool:
    if invited_user_id <= 0 or inviter_user_id <= 0 or invited_user_id == inviter_user_id:
        return False

    await _db_connect()
    assert _db_pool is not None

    ts = now_iso()
    async with _db_pool.acquire() as conn:
        async with conn.transaction():
            await conn.execute("SELECT pg_advisory_xact_lock($1)", invited_user_id)

            await conn.execute(
                f"""
                INSERT INTO users (
                    user_id, username, first_seen, last_seen, starts, requests, receipt_checks,
                    receipt_quota, referrals_total, referral_reward_total
                )
                VALUES ($1, NULL, $2, $2, 0, 0, 0, {INITIAL_RECEIPT_QUOTA}, 0, 0)
                ON CONFLICT (user_id) DO NOTHING
                """,
                inviter_user_id, ts
            )
            await conn.execute(
                f"""
                INSERT INTO users (
                    user_id, username, first_seen, last_seen, starts, requests, receipt_checks,
                    receipt_quota, referrals_total, referral_reward_total
                )
                VALUES ($1, NULL, $2, $2, 0, 0, 0, {INITIAL_RECEIPT_QUOTA}, 0, 0)
                ON CONFLICT (user_id) DO NOTHING
                """,
                invited_user_id, ts
            )

            existing_ref = await conn.fetchrow(
                "SELECT inviter_user_id FROM referrals WHERE invited_user_id = $1",
                invited_user_id
            )
            if existing_ref is not None:
                return False

            row = await conn.fetchrow(
                """
                UPDATE users
                SET invited_by = $2
                WHERE user_id = $1
                  AND invited_by IS NULL
                  AND user_id <> $2
                RETURNING user_id
                """,
                invited_user_id, inviter_user_id
            )
            if row is None:
                return False

            await conn.execute(
                f"""
                INSERT INTO referrals (invited_user_id, inviter_user_id, created_at, reward_amount)
                VALUES ($1, $2, $3, {REFERRAL_REWARD_AMOUNT})
                """,
                invited_user_id, inviter_user_id, ts
            )
            return True


async def get_user_state(user_id: int):
    return await db_fetchone("SELECT * FROM users WHERE user_id = $1", (user_id,))


async def get_user_receipt_access_status(user_id: int) -> dict:
    row = await db_fetchone(
        "SELECT receipt_quota, unlimited_until FROM users WHERE user_id = $1",
        (user_id,)
    )
    quota = int(row["receipt_quota"]) if row else 0
    unlimited_until = row["unlimited_until"] if row else None
    return {
        "quota": quota,
        "unlimited_active": is_unlimited_active(unlimited_until),
        "unlimited_until": unlimited_until,
    }


async def consume_receipt_access(user_id: int) -> dict:
    await _db_connect()
    assert _db_pool is not None

    async with _db_pool.acquire() as conn:
        async with conn.transaction():
            row = await conn.fetchrow(
                "SELECT receipt_quota, unlimited_until FROM users WHERE user_id = $1 FOR UPDATE",
                user_id
            )
            if row is None:
                return {
                    "allowed": False,
                    "quota": 0,
                    "unlimited_active": False,
                    "unlimited_until": None,
                    "quota_consumed": False,
                }

            quota = int(row["receipt_quota"])
            unlimited_until = row["unlimited_until"]

            # Invariant: active unlimited access never consumes receipt_quota.
            if is_unlimited_active(unlimited_until):
                return {
                    "allowed": True,
                    "quota": quota,
                    "unlimited_active": True,
                    "unlimited_until": unlimited_until,
                    "quota_consumed": False,
                }

            # Invariant: when unlimited is inactive and quota > 0, consume exactly one check.
            if quota > 0:
                upd = await conn.fetchrow(
                    "UPDATE users SET receipt_quota = receipt_quota - 1 WHERE user_id = $1 RETURNING receipt_quota",
                    user_id
                )
                new_quota = int(upd["receipt_quota"])
                return {
                    "allowed": True,
                    "quota": new_quota,
                    "unlimited_active": False,
                    "unlimited_until": unlimited_until,
                    "quota_consumed": True,
                }

            return {
                "allowed": False,
                "quota": 0,
                "unlimited_active": False,
                "unlimited_until": unlimited_until,
                "quota_consumed": False,
            }


async def refund_receipt_access(user_id: int, access: dict | None):
    if not access:
        return
    if not access.get("quota_consumed"):
        return
    if access.get("unlimited_active"):
        return

    await _db_connect()
    assert _db_pool is not None
    async with _db_pool.acquire() as conn:
        await conn.execute(
            "UPDATE users SET receipt_quota = receipt_quota + 1 WHERE user_id = $1",
            user_id
        )


def build_receipt_access_lines(access_status: dict) -> list[str]:
    lines = [f"🧾 <b>Доступно проверок чеков</b>: {access_status['quota']}"]
    if access_status["unlimited_active"]:
        lines.append(f"♾️ <b>Безлимит активен до</b>: {format_access_until(access_status['unlimited_until'])}")
    else:
        lines.append("♾️ <b>Безлимит</b>: не активен")
    lines.append(f"🎁 За 1 подтверждённого пользователя начисляется +{REFERRAL_REWARD_AMOUNT} доступов")
    lines.append(
        "ℹ️ Подтверждённый пользователь — тот, кто пришёл по ссылке и выполнил действие: "
        "проверил карту или чек"
    )
    return lines


def build_unlimited_offer_lines() -> list[str]:
    return [
        f"♾️ Безлимит на {UNLIMITED_PLAN_DAYS} дней — {UNLIMITED_PRICE_USDT} USDT",
        f"Для активации: {SUPPORT_USERNAME}",
    ]


async def build_receipt_access_text(user_id: int, bot) -> str:
    access_status = await get_user_receipt_access_status(user_id)
    referral_link = await get_personal_referral_link(bot, user_id)
    lines = build_receipt_access_lines(access_status)
    lines.extend(["", f"🔗 <b>Твоя реферальная ссылка</b>:", referral_link])
    return "\n".join(lines)


async def build_no_receipt_access_text(user_id: int, bot) -> str:
    referral_link = await get_personal_referral_link(bot, user_id)
    return (
        "🧾 <b>Доступно проверок</b>: 0\n\n"
        f"👥 Пригласи 1 пользователя и получи +{REFERRAL_REWARD_AMOUNT}\n"
        f"♾️ Безлимит на {UNLIMITED_PLAN_DAYS} дней — {UNLIMITED_PRICE_USDT} USDT\n"
        f"Для активации: {SUPPORT_USERNAME}\n\n"
        f"🔗 <b>Твоя реферальная ссылка</b>:\n{referral_link}"
    )


def build_receipt_result_text(result_text: str, access: dict) -> str:
    if access["unlimited_active"]:
        return (
            f"{result_text}\n\n"
            f"♾️ Действует безлимит на проверку чеков до {format_access_until(access['unlimited_until'])}."
        )
    return f"{result_text}\n\n🧾 Доступно проверок чеков: {access['quota']}"


def render_pdf_result_message(result: "PdfAnalysisResult", access: dict) -> str:
    status = safe_str(result.verdict_status) or "inconclusive"
    header_map = {
        "edited": "❌ <b>Высокий риск редактирования</b>",
        "suspicious": "🔴 <b>Повышенный риск</b>",
        "inconclusive": "🟠 <b>Нужна дополнительная проверка</b>",
        "clean": "🟢 <b>Низкий риск</b>",
    }
    header = header_map.get(status, header_map["inconclusive"])

    summary = result.critical_fields_summary or {}
    reasons_set = {safe_str(r) for r in (result.verdict_reasons or []) if safe_str(r)}
    comments: list[str] = []
    comments_seen: set[str] = set()

    def add_comment(text: str):
        normalized = normalize_text_for_match(text)
        if not normalized or normalized in comments_seen:
            return
        comments_seen.add(normalized)
        comments.append(text)

    limitation_set = set(result.limitations or [])
    # 1) reason-aware комментарии (высший приоритет).
    if reasons_set.intersection({"high_edit_score", "strong_forensic_combo"}):
        add_comment("Обнаружены признаки возможного вмешательства в PDF")
    if reasons_set.intersection({"template_semantic_suspicion", "suspicious_structure_or_semantics"}):
        add_comment("Структура или набор реквизитов выглядят нетипично слабо")
    has_limitation_reason = bool(
        reasons_set.intersection({"severe_limitation", "low_analysis_confidence", "insufficient_text_context", "image_or_mixed_low_text_confidence"})
    )
    if has_limitation_reason:
        add_comment("Анализ ограничен по качеству извлечённых данных")
    if "insufficient_confidence_for_clean" in reasons_set:
        add_comment("Данных недостаточно для полностью уверенного вывода")

    # 2) Конфликты и частичное извлечение.
    if summary.get("conflicting_amount_candidates") or summary.get("conflicting_date_candidates"):
        add_comment("Обнаружены конфликтующие сумма или дата")
    if "limited_text_extraction" in limitation_set and not has_limitation_reason:
        add_comment("PDF распознан частично")

    # 3) Вторичные информативные комментарии.
    found_fields = []
    if summary.get("amount_found"):
        found_fields.append("сумма")
    if summary.get("date_found"):
        found_fields.append("дата")
    if summary.get("time_found"):
        found_fields.append("время")
    if summary.get("status_found"):
        found_fields.append("статус")
    if summary.get("operation_id_found"):
        found_fields.append("ID операции")
    if found_fields:
        add_comment("Найдены ключевые поля: " + ", ".join(found_fields[:5]))
    if result.ocr_used:
        add_comment("Для части страниц использовалось OCR")

    # 4) Общий мягкий совет.
    if status in {"edited", "suspicious", "inconclusive"}:
        add_comment("Лучше запросить дополнительное подтверждение перевода")
    elif status == "clean":
        if limitation_set.intersection({"limited_text_extraction", "ocr_not_available", "ocr_low_text", "native_text_unavailable"}):
            add_comment("Явных следов редактирования не найдено, но итог лучше сверять с фактом поступления")
        else:
            add_comment("Явных следов редактирования не найдено")

    if len(comments) < 2:
        add_comment("Итог лучше сверять с фактом поступления")
    comments = comments[:4]

    lines = [header, "", result.verdict, ""]
    for item in comments:
        lines.append(f"• {item}")

    lines.append("")
    if access["unlimited_active"]:
        lines.append(f"♾️ Действует безлимит на проверку чеков до {format_access_until(access['unlimited_until'])}.")
    else:
        lines.append(f"🧾 Доступно проверок чеков: {access['quota']}")

    return "\n".join(lines)


async def build_invite_text(user_id: int, bot) -> str:
    referral_link = await get_personal_referral_link(bot, user_id)
    return (
        "👥 <b>Пригласи пользователя</b>\n\n"
        f"🎁 За 1 подтверждённого пользователя начисляется +{REFERRAL_REWARD_AMOUNT} доступов.\n"
        "ℹ️ Подтверждённый пользователь — тот, кто пришёл по ссылке и выполнил действие: "
        "проверил карту или чек.\n\n"
        f"🔗 <b>Твоя реферальная ссылка</b>:\n{referral_link}"
    )


async def mark_referral_qualified_and_reward(invited_user_id: int) -> int | None:
    await _db_connect()
    assert _db_pool is not None

    ts = now_iso()
    async with _db_pool.acquire() as conn:
        async with conn.transaction():
            ref = await conn.fetchrow(
                """
                SELECT inviter_user_id, rewarded, reward_amount
                FROM referrals
                WHERE invited_user_id = $1
                FOR UPDATE
                """,
                invited_user_id
            )
            if ref is None:
                return None

            if int(ref["rewarded"]) == 1:
                return None

            inviter_user_id = int(ref["inviter_user_id"])
            reward_amount = int(ref["reward_amount"])

            updated = await conn.fetchrow(
                """
                UPDATE referrals
                SET qualified_at = COALESCE(qualified_at, $2),
                    rewarded = 1,
                    rewarded_at = $2
                WHERE invited_user_id = $1
                  AND rewarded = 0
                RETURNING inviter_user_id
                """,
                invited_user_id, ts
            )
            if updated is None:
                return None

            await conn.execute(
                f"""
                INSERT INTO users (
                    user_id, username, first_seen, last_seen, starts, requests, receipt_checks,
                    receipt_quota, referrals_total, referral_reward_total
                )
                VALUES ($1, NULL, $2, $2, 0, 0, 0, {INITIAL_RECEIPT_QUOTA}, 0, 0)
                ON CONFLICT (user_id) DO NOTHING
                """,
                inviter_user_id, ts
            )
            await conn.execute(
                """
                UPDATE users
                SET receipt_quota = receipt_quota + $2,
                    referrals_total = referrals_total + 1,
                    referral_reward_total = referral_reward_total + $2
                WHERE user_id = $1
                """,
                inviter_user_id, reward_amount
            )
            return inviter_user_id


async def notify_inviter_reward(bot, inviter_user_id: int, reward_amount: int):
    try:
        await bot.send_message(
            chat_id=inviter_user_id,
            text=(
                "🎉 Твой реферал выполнил первое действие.\n"
                f"Тебе начислено +{reward_amount} доступов на проверку чеков."
            )
        )
    except Exception:
        logger.exception("Не удалось уведомить пригласившего user_id=%s", inviter_user_id)


async def grant_unlimited_access(user_id: int, days: int, plan_name: str, source: str):
    await _db_connect()
    assert _db_pool is not None

    if days <= 0:
        return

    now_dt = datetime.now(TZ)
    ts = now_iso()

    async with _db_pool.acquire() as conn:
        async with conn.transaction():
            await conn.execute(
                f"""
                INSERT INTO users (
                    user_id, username, first_seen, last_seen, starts, requests, receipt_checks,
                    receipt_quota, referrals_total, referral_reward_total
                )
                VALUES ($1, NULL, $2, $2, 0, 0, 0, {INITIAL_RECEIPT_QUOTA}, 0, 0)
                ON CONFLICT (user_id) DO NOTHING
                """,
                user_id, ts
            )
            row = await conn.fetchrow(
                "SELECT unlimited_until FROM users WHERE user_id = $1 FOR UPDATE",
                user_id
            )
            if row is None:
                raise RuntimeError(f"Failed to create or load user {user_id} in grant_unlimited_access")

            current_until = _parse_iso_dt(row["unlimited_until"])
            # Extend from current unlimited_until when active; otherwise extend from now.
            base_dt = current_until if current_until and current_until > now_dt else now_dt
            new_until = base_dt + timedelta(days=days)

            await conn.execute(
                """
                UPDATE users
                SET unlimited_until = $2,
                    paid_plan = $3,
                    paid_source = $4
                WHERE user_id = $1
                """,
                user_id, new_until.isoformat(timespec="seconds"), plan_name, source
            )


async def track_event_bg(user_id: int, username: str | None, event_type: str):
    """
    event_type:
    - start
    - card_request
    - receipt_request
    """
    if event_type not in ("start", "card_request", "receipt_request"):
        return

    await _db_connect()
    assert _db_pool is not None

    day = today_str()
    ts = now_iso()
    new_username = username if username else None

    async with _db_pool.acquire() as conn:
        async with conn.transaction():
            await conn.execute(
                """
                INSERT INTO daily (day, starts, requests, unique_users, receipt_checks)
                VALUES ($1, 0, 0, 0, 0)
                ON CONFLICT (day) DO NOTHING
                """,
                day
            )

            # Keep quota/referral/subscription fields intact on conflict:
            # only touch username and last_seen in tracking events.
            await conn.execute(
                """
                INSERT INTO users (user_id, username, first_seen, last_seen, starts, requests, receipt_checks)
                VALUES ($1, $2, $3, $4, 0, 0, 0)
                ON CONFLICT (user_id) DO UPDATE SET
                    username  = COALESCE(EXCLUDED.username, users.username),
                    last_seen = EXCLUDED.last_seen
                """,
                user_id, new_username, ts, ts
            )

            inserted = await conn.fetchrow(
                """
                INSERT INTO user_day (user_id, day)
                VALUES ($1, $2)
                ON CONFLICT DO NOTHING
                RETURNING 1
                """,
                user_id, day
            )

            if inserted is not None:
                await conn.execute(
                    "UPDATE daily SET unique_users = unique_users + 1 WHERE day = $1",
                    day
                )

            if event_type == "start":
                await conn.execute(
                    "UPDATE users SET starts = starts + 1, last_seen = $1 WHERE user_id = $2",
                    ts, user_id
                )
                await conn.execute(
                    "UPDATE daily SET starts = starts + 1 WHERE day = $1",
                    day
                )
            elif event_type == "card_request":
                await conn.execute(
                    "UPDATE users SET requests = requests + 1, last_seen = $1 WHERE user_id = $2",
                    ts, user_id
                )
                await conn.execute(
                    "UPDATE daily SET requests = requests + 1 WHERE day = $1",
                    day
                )
            elif event_type == "receipt_request":
                await conn.execute(
                    "UPDATE users SET receipt_checks = receipt_checks + 1, last_seen = $1 WHERE user_id = $2",
                    ts, user_id
                )
                await conn.execute(
                    "UPDATE daily SET receipt_checks = receipt_checks + 1 WHERE day = $1",
                    day
                )


async def get_stats_text() -> str:
    day = today_str()
    await ensure_daily_row(day)

    await _db_connect()
    assert _db_pool is not None

    async with _db_pool.acquire() as conn:
        total_users = await conn.fetchrow("SELECT COUNT(*) AS c FROM users")
        total_starts = await conn.fetchrow("SELECT COALESCE(SUM(starts),0) AS s FROM users")
        total_card_requests = await conn.fetchrow("SELECT COALESCE(SUM(requests),0) AS r FROM users")
        total_receipt_checks = await conn.fetchrow("SELECT COALESCE(SUM(receipt_checks),0) AS r FROM users")
        today_row = await conn.fetchrow(
            "SELECT starts, requests, unique_users, receipt_checks FROM daily WHERE day = $1",
            day
        )
        users_with_invited_by = await conn.fetchrow("SELECT COUNT(*) AS c FROM users WHERE invited_by IS NOT NULL")
        confirmed_referrals = await conn.fetchrow("SELECT COUNT(*) AS c FROM referrals WHERE rewarded = 1")
        referral_rewards_total = await conn.fetchrow(
            "SELECT COALESCE(SUM(reward_amount),0) AS s FROM referrals WHERE rewarded = 1"
        )
        unlimited_rows = await conn.fetch("SELECT unlimited_until FROM users WHERE unlimited_until IS NOT NULL")

    today_data = today_row or {"starts": 0, "requests": 0, "unique_users": 0, "receipt_checks": 0}
    starts_today = int(today_data.get("starts") or 0)
    card_requests_today = int(today_data.get("requests") or 0)
    receipt_checks_today = int(today_data.get("receipt_checks") or 0)
    dau_today = int(today_data.get("unique_users") or 0)
    active_unlimited_users = sum(1 for row in unlimited_rows if is_unlimited_active(row["unlimited_until"]))

    return (
        "📊 <b>Статистика</b>\n\n"
        f"👥 <b>Пользователей всего</b>: {int(total_users['c'])}\n"
        f"▶️ <b>/start за всё время</b>: {int(total_starts['s'])}\n"
        f"💳 <b>Проверок карт за всё время</b>: {int(total_card_requests['r'])}\n"
        f"🧾 <b>Проверок чеков за всё время</b>: {int(total_receipt_checks['r'])}\n"
        f"🔗 <b>Пользователей с invited_by</b>: {int(users_with_invited_by['c'])}\n"
        f"✅ <b>Подтверждённых рефералов</b>: {int(confirmed_referrals['c'])}\n"
        f"🎁 <b>Выдано реферальных проверок</b>: {int(referral_rewards_total['s'])}\n"
        f"♾️ <b>Активных безлимитов</b>: {active_unlimited_users}\n\n"
        f"📅 <b>Сегодня ({day})</b>\n"
        f"👤 <b>DAU</b>: {dau_today}\n"
        f"▶️ <b>/start</b>: {starts_today}\n"
        f"💳 <b>Проверок карт</b>: {card_requests_today}\n"
        f"🧾 <b>Проверок чеков</b>: {receipt_checks_today}"
    )


# =========================
# BIN DB
# =========================
def load_db():
    try:
        csv_path = "full_bins.csv"
        if not os.path.exists(csv_path):
            logger.info("Распаковываю архив full_bins.zip...")
            with zipfile.ZipFile("full_bins.zip", "r") as zip_ref:
                zip_ref.extractall()
                logger.info("Архив успешно распакован")

        with open(csv_path, newline="", encoding="utf-8") as f:
            reader = csv.DictReader(f)
            for row in reader:
                bin_code = row.get("BIN")
                if not bin_code:
                    continue
                bin_db[bin_code] = (
                    row.get("Brand") or "Unknown",
                    row.get("Issuer") or "Unknown",
                    row.get("CountryName") or "Unknown",
                )

        logger.info(f"Загружено {len(bin_db)} BIN-кодов")
        return True
    except Exception as e:
        logger.error(f"Ошибка загрузки базы: {str(e)}")
        return False


def get_card_scheme(bin_code: str) -> str:
    if not bin_code.isdigit() or len(bin_code) < 6:
        return "Unknown"

    first_digit = int(bin_code[0])
    first_two = int(bin_code[:2])
    first_four = int(bin_code[:4])

    if first_digit == 4:
        return "Visa"
    elif 51 <= first_two <= 55 or 2221 <= first_four <= 2720:
        return "MasterCard"
    elif 2200 <= first_four <= 2204:
        return "МИР"
    return "Unknown"


# =========================
# Rapira rate
# =========================
async def fetch_rapira_usdt_rub() -> dict | None:
    now_ts = monotonic_now()
    if _rapira_cache["data"] is not None and (now_ts - _rapira_cache["ts"]) < _RAPIRA_CACHE_SECONDS:
        return _rapira_cache["data"]

    url = "https://api.rapira.net/open/market/rates"
    try:
        session = await get_http_session()
        async with session.get(url, headers={"Accept": "application/json"}) as resp:
            if resp.status != 200:
                return None
            data = await resp.json()
            items = data.get("data", [])
            for item in items:
                if item.get("symbol") == "USDT/RUB":
                    _rapira_cache["ts"] = now_ts
                    _rapira_cache["data"] = item
                    return item
    except Exception as e:
        logger.error(f"Rapira API error: {e}")
    return None


# =========================
# BINLIST cache/helper
# =========================
async def fetch_binlist_info(bin_code: str) -> tuple[str, str]:
    cached = _binlist_cache.get(bin_code)
    now_ts = monotonic_now()
    if cached and (now_ts - cached[0]) < _BINLIST_CACHE_SECONDS:
        data = cached[1]
        return (
            data.get("issuer", "Unknown"),
            data.get("country", "Unknown"),
        )

    issuer = "Unknown"
    country = "Unknown"

    try:
        url = f"https://lookup.binlist.net/{bin_code}"
        headers = {"Accept-Version": "3"}
        session = await get_http_session()

        timeout = aiohttp.ClientTimeout(total=1.5, connect=0.8, sock_connect=0.8, sock_read=1.0)
        async with session.get(url, headers=headers, timeout=timeout) as resp:
            if resp.status == 200:
                data = await resp.json()
                issuer = data.get("bank", {}).get("name", issuer) or "Unknown"
                country = data.get("country", {}).get("name", country) or "Unknown"
                _binlist_cache[bin_code] = (
                    now_ts,
                    {"issuer": issuer, "country": country},
                )
    except Exception as e:
        logger.error(f"BINLIST API error: {str(e)}")

    return issuer, country


# =========================
# PAN hash counter
# =========================
def pan_to_hash(pan_digits: str) -> str:
    salt = CARD_HASH_SALT or "default_salt_change_me"
    digest = hashlib.sha256((salt + pan_digits).encode("utf-8")).digest()
    return base64.urlsafe_b64encode(digest).decode("ascii").rstrip("=")[:32]


async def get_pan_info_and_inc(h: str) -> tuple[int, bool]:
    await _db_connect()
    assert _db_pool is not None

    async with _db_pool.acquire() as conn:
        async with conn.transaction():
            row_cnt = await conn.fetchrow(
                """
                INSERT INTO pan_hash (h, cnt)
                VALUES ($1, 1)
                ON CONFLICT (h) DO UPDATE SET cnt = pan_hash.cnt + 1
                RETURNING cnt
                """,
                h
            )

            row_flag = await conn.fetchrow(
                "SELECT is_problem FROM pan_flags WHERE h = $1",
                h
            )

    cnt = int(row_cnt["cnt"])
    is_problem = bool(row_flag and int(row_flag["is_problem"]) == 1)
    return cnt, is_problem


async def set_pan_flag(h: str, user_id: int, is_problem: bool):
    await db_execute(
        """
        INSERT INTO pan_flags (h, is_problem, flagged_at, flagged_by)
        VALUES ($1, $2, $3, $4)
        ON CONFLICT (h) DO UPDATE SET
            is_problem=EXCLUDED.is_problem,
            flagged_at=EXCLUDED.flagged_at,
            flagged_by=EXCLUDED.flagged_by
        """,
        (h, 1 if is_problem else 0, now_iso(), user_id)
    )


# =========================
# PDF check helpers
# =========================
AMOUNT_PATTERN = re.compile(
    r'(?<!\d)(\d{1,3}(?:[\s.,]\d{3})*(?:[\s.,]\d{2})?)\s?(₽|RUB|руб|Руб|р\.?|KZT|₸|тенге|UZS|сум|TJS|сомони|KGS|сом|BYN|Br|AMD|֏|AZN|₼|GEL|₾|USD|\$|EUR|€|UAH|грн|₴)',
    flags=re.IGNORECASE
)
DATE_PATTERN = re.compile(r'\b(?:\d{2}[./-]\d{2}[./-]\d{2,4}|\d{4}[./-]\d{2}[./-]\d{2})\b')
TIME_PATTERN = re.compile(r'(?<!\d)\b(?:[01]?\d|2[0-3]):[0-5]\d(?::[0-5]\d)?\b(?!\d)')
CARD_MASK_PATTERN = re.compile(
    r'(?:\*{3,}\s*\d{4}|\*\d{4}|[•●]{3,}\s*\d{4}|\d{4}\s*\d{2}\*{2}\s*\*{4}\s*\d{4}|\d{4}[ *•●]{2,}\d{4})'
)
OPERATION_ID_PATTERN = re.compile(
    r'\b(?:operation\s*id|transaction\s*id|reference|rrn|txn|auth(?:\s*code)?|order\s*id|номер\s*операции)\b[:\s#-]*([A-Z0-9-]{4,})?',
    flags=re.IGNORECASE
)
PHONE_PATTERN = re.compile(
    r'(?<!\w)(?:\+?\d{1,4}[\s\-()]*)?(?:\d[\s\-()]*){8,15}(?!\w)'
)
IBAN_PATTERN = re.compile(r'\b[A-Z]{2}\d{2}[A-Z0-9]{10,30}\b', flags=re.IGNORECASE)
ACCOUNT_PATTERN = re.compile(
    r'\b(?:account|acct|сч[её]т|номер\s*сч[её]та|beneficiary\s*account)\b[:\s#-]*([A-Z0-9]{8,34})?\b',
    flags=re.IGNORECASE
)
STATUS_PATTERN = re.compile(
    r'\b(?:status|статус|успешно|успешный|выполнен|выполнено|success(?:ful)?|completed|approved|paid|'
    r'failed|declined|rejected|error|pending|processing|отклонен|ошибка|в\s*обработке)\b',
    flags=re.IGNORECASE
)
CURRENCY_TOKEN_PATTERN = re.compile(
    r'\b(?:RUB|KZT|UZS|TJS|KGS|BYN|AMD|AZN|GEL|USD|EUR|UAH|руб|р\.?|тенге|сум|сом|сомони|грн|Br)\b|[₽₸֏₼₾₴$€]',
    flags=re.IGNORECASE
)
TRANSACTION_CONTEXT_PATTERN = re.compile(
    r'\b(?:transaction|payment|operation|reference|rrn|auth(?:\s*code)?|order|операц|перевод(?:\s+клиенту)?|платеж|чек|receipt|invoice|kaspi|каспи|получател\w*|отправител\w*|recipient|sender)\b',
    flags=re.IGNORECASE
)
OPERATION_ID_CAPTURE_PATTERN = re.compile(
    r'\b(?:operation\s*id|transaction\s*id|reference|rrn|txn|auth(?:\s*code)?|order\s*id|номер\s*операции)\b'
    r'[:\s#-]*([A-Z0-9-]{3,40})?',
    flags=re.IGNORECASE
)

# Критические поля для forensic-проверки: их чаще всего точечно подменяют в чеке.
# Важно: наличие этих слов само по себе не подозрительно и не повышает score.
CRITICAL_KEYWORDS = [
    "сумма", "итого", "к оплате", "перевод", "получатель", "отправитель",
    "дата", "время", "статус", "операция", "номер операции", "чек", "комиссия",
    "банк", "карта", "счёт", "счет", "реквизиты", "телефон", "номер телефона",
    "iban", "beneficiary", "recipient", "sender", "account", "phone", "mobile",
    "beneficiary account", "reference", "transaction", "payment", "receipt",
    "total", "amount", "status", "fee", "auth", "rrn"
]

SUSPICIOUS_PRODUCERS = [
    "Microsoft Word",
    "LibreOffice",
    "OpenOffice",
    "WPS",
    "Photoshop",
    "Illustrator",
    "Corel",
    "Canva",
    "Writer",
    "iLovePDF",
    "Sejda",
    "Smallpdf",
    "Foxit",
    "Nitro",
    "PDFelement",
]

SUSPICIOUS_CREATORS = [
    "Word",
    "LibreOffice",
    "Photoshop",
    "Illustrator",
    "Canva",
    "Foxit",
    "Nitro",
    "PDFelement",
]


def count_incremental_updates(raw_bytes: bytes) -> int:
    try:
        text = raw_bytes.decode("latin-1", errors="ignore")
        startxref_count = text.count("startxref")
        xref_count = text.count("\nxref")
        trailer_count = text.count("trailer")
        return max(startxref_count, xref_count, trailer_count)
    except Exception:
        return 0


def detect_editor_hints(metadata: dict) -> bool:
    producer = safe_str(metadata.get("producer"))
    creator = safe_str(metadata.get("creator"))

    for item in SUSPICIOUS_PRODUCERS:
        if item.lower() in producer.lower():
            return True

    for item in SUSPICIOUS_CREATORS:
        if item.lower() in creator.lower():
            return True

    return False


def is_amount_like(text: str) -> bool:
    return bool(AMOUNT_PATTERN.search(text or ""))


def is_date_like(text: str) -> bool:
    return bool(DATE_PATTERN.search(text or ""))


def normalize_text_for_match(text: str) -> str:
    text = safe_str(text).replace("\u00a0", " ").replace("ё", "е").replace("Ё", "Е")
    text = re.sub(r"\s+", " ", text).strip().lower()
    return text


def is_time_like(text: str) -> bool:
    return bool(TIME_PATTERN.search(text or ""))


def is_card_mask_like(text: str) -> bool:
    return bool(CARD_MASK_PATTERN.search(text or ""))


def is_operation_id_like(text: str) -> bool:
    raw = safe_str(text)
    txt = normalize_text_for_match(raw)
    if OPERATION_ID_PATTERN.search(txt):
        return True
    # Осторожный fallback: только mixed alnum-токены, не чисто numeric.
    for token in re.findall(r"\b[A-Z0-9-]{10,24}\b", raw.upper()):
        compact = token.replace("-", "")
        if len(compact) < 10 or compact.isdigit():
            continue
        if re.search(r"[A-Z]", compact) and re.search(r"\d", compact):
            return True
    return False


def is_phone_like(text: str) -> bool:
    txt = safe_str(text)
    if not PHONE_PATTERN.search(txt):
        return False
    digits = re.sub(r"\D", "", txt)
    if not (9 <= len(digits) <= 15):
        return False

    normalized = normalize_text_for_match(txt)
    has_phone_kw = any(k in normalized for k in ("phone", "mobile", "телефон", "номер телефона"))
    has_phone_format = any(ch in txt for ch in ("+", "(", ")", "-", " "))

    # Без keyword и без форматных маркеров длинные numeric-поля не считаем телефоном.
    if not has_phone_kw and not has_phone_format:
        return False
    return True


def is_iban_like(text: str) -> bool:
    compact = re.sub(r"[\s-]+", "", safe_str(text).upper())
    return bool(IBAN_PATTERN.search(compact))


def is_account_like(text: str) -> bool:
    txt = safe_str(text)
    if ACCOUNT_PATTERN.search(txt):
        return True
    compact = re.sub(r"[\s-]+", "", txt.upper())
    # Осторожный fallback: только явные mixed alnum account-like токены.
    for token in re.findall(r"\b[A-Z0-9]{14,34}\b", compact):
        if token.isdigit():
            continue
        if re.search(r"[A-Z]", token) and re.search(r"\d", token):
            return True
    return False


def contains_critical_keyword(text: str) -> bool:
    normalized = normalize_text_for_match(text)
    return any(keyword in normalized for keyword in CRITICAL_KEYWORDS)


def intersects(r1, r2) -> bool:
    x0 = max(r1[0], r2[0])
    y0 = max(r1[1], r2[1])
    x1 = min(r1[2], r2[2])
    y1 = min(r1[3], r2[3])
    return x1 > x0 and y1 > y0


def rect_area(rect) -> float:
    return max(0.0, (rect[2] - rect[0]) * (rect[3] - rect[1]))


def collect_native_text(doc: fitz.Document) -> str:
    parts = []
    for page in doc:
        text = page.get_text("text")
        if text:
            parts.append(text)
    return "\n".join(parts).strip()


def _receipt_semantic_groups_hits(text: str) -> tuple[int, set[str]]:
    groups = [
        ("amount", ("amount", "total", "итого", "к оплате", "сумма", "оплате")),
        ("date_time", ("date", "дата", "time", "время")),
        ("receipt", ("чек", "receipt", "квитан", "invoice")),
        ("operation", ("операц", "transaction", "payment", "reference", "rrn", "auth", "order")),
        ("card", ("card", "карта", "visa", "mastercard", "мир", "pan")),
        ("bank", ("bank", "банк")),
        ("currency", ("rub", "руб", "kzt", "uzs", "usd", "eur", "uah", "byn", "сом", "тенге")),
    ]

    hits = 0
    found_groups = set()
    for group_name, words in groups:
        if any(w in text for w in words):
            hits += 1
            found_groups.add(group_name)
    return hits, found_groups


def _unique_limited(items: list[str], limit: int = 12) -> list[str]:
    out = []
    seen = set()
    for item in items:
        normalized = re.sub(r"\s+", " ", safe_str(item)).strip()
        if not normalized:
            continue
        key = normalized.lower()
        if key in seen:
            continue
        seen.add(key)
        out.append(normalized)
        if len(out) >= limit:
            break
    return out


def _normalize_compact(value: str) -> str:
    return re.sub(r"[\s\-]+", "", safe_str(value)).upper()


def _normalize_amount_candidate(value: str) -> str:
    raw = safe_str(value).replace("\u00a0", " ").strip()
    m = re.search(r"\d[\d\s.,]*", raw)
    if not m:
        return normalize_text_for_match(raw)

    num = re.sub(r"\s+", "", m.group(0))
    if not num:
        return normalize_text_for_match(raw)

    last_dot = num.rfind(".")
    last_comma = num.rfind(",")
    dec_pos = max(last_dot, last_comma)
    if dec_pos >= 0 and len(num) - dec_pos - 1 == 2:
        int_part = re.sub(r"[^\d]", "", num[:dec_pos])
        dec_part = re.sub(r"[^\d]", "", num[dec_pos + 1:])
        if int_part and dec_part:
            return f"{int_part}.{dec_part}"

    return re.sub(r"[^\d]", "", num)


def _normalize_date_candidate(value: str) -> str:
    raw = safe_str(value).strip()
    m = re.match(r"^(\d{2,4})[./-](\d{2})[./-](\d{2,4})$", raw)
    if not m:
        return normalize_text_for_match(raw)

    a, b, c = m.group(1), m.group(2), m.group(3)
    if len(a) == 4:
        year, month, day = a, b, c
    else:
        day, month, year = a, b, c
        if len(year) == 2:
            year = f"20{year}"
    return f"{year.zfill(4)}-{month.zfill(2)}-{day.zfill(2)}"


def _extract_currency_candidates(text: str) -> list[str]:
    candidates = [m.group(0).strip() for m in CURRENCY_TOKEN_PATTERN.finditer(text)]
    # Дополняем из amount-мэтчей безопасно (без жёсткой привязки к group index).
    for m in AMOUNT_PATTERN.finditer(text):
        groups = m.groups()
        if len(groups) >= 2:
            token = safe_str(groups[-1]).strip()
            if token:
                candidates.append(token)
    return _unique_limited(candidates)


CONTEXTUAL_AMOUNT_KEYWORD_PATTERN = re.compile(
    r'\b(?:сумма|сумма\s+перевода|итого|к\s*оплате|на\s*сумму|amount|total|transfer\s+amount)\b',
    flags=re.IGNORECASE
)
CONTEXTUAL_AMOUNT_NUMBER_PATTERN = re.compile(
    r'(?<!\d)(?:\d{1,3}(?:[\s\u00a0.,]\d{3})+(?:[.,]\d{2})?|\d{1,7}[.,]\d{2}|\d{3,7})(?!\d)'
)


def _extract_contextual_amount_candidates(text: str) -> list[str]:
    candidates: list[str] = []
    for line in safe_str(text).splitlines():
        normalized_line = safe_str(line)
        if not normalized_line.strip():
            continue
        if not CONTEXTUAL_AMOUNT_KEYWORD_PATTERN.search(normalized_line):
            continue

        keyword_positions = [m.start() for m in CONTEXTUAL_AMOUNT_KEYWORD_PATTERN.finditer(normalized_line)]
        for number_match in CONTEXTUAL_AMOUNT_NUMBER_PATTERN.finditer(normalized_line):
            start, end = number_match.span()
            if keyword_positions and min(abs(start - pos) for pos in keyword_positions) > 28:
                continue

            nearby = normalized_line[max(0, start - 8): min(len(normalized_line), end + 8)]
            if DATE_PATTERN.search(nearby) or TIME_PATTERN.search(nearby):
                continue
            if re.search(r"\d{1,2}[./-]\d{1,2}[./-]\d{2,4}", nearby):
                continue
            guard_window = normalized_line[max(0, start - 24): min(len(normalized_line), end + 24)]
            if re.search(
                r"\b(?:phone|телефон|id|reference|rrn|order|txn|auth|код|номер\s*операции)\b",
                guard_window,
                flags=re.IGNORECASE,
            ):
                continue

            candidate = number_match.group(0).strip()
            if candidate:
                candidates.append(candidate)
    return _unique_limited(candidates)


def _is_generic_operation_id(value: str) -> bool:
    compact = _normalize_compact(value)
    if not compact:
        return True
    lowered = compact.lower()
    if lowered in {"na", "n/a", "none", "null", "test", "demo", "unknown"}:
        return True
    if re.fullmatch(r"(0+|1+|9+|1234+|9876+)", compact):
        return True
    if len(set(compact)) <= 2 and len(compact) >= 6:
        return True
    return False


def _is_valid_operation_id_candidate(candidate: str, strict: bool = False) -> bool:
    value = safe_str(candidate).strip(":-# ")
    compact = _normalize_compact(value)
    if not compact:
        return False
    if _is_generic_operation_id(compact):
        return False
    if compact.lower() in {
        "id", "operationid", "transactionid", "reference", "rrn", "txn", "auth", "authcode", "orderid", "code"
    }:
        return False
    if is_date_like(value) or is_time_like(value):
        return False
    if is_iban_like(value) or is_account_like(value) or is_card_mask_like(value):
        return False

    has_alpha = bool(re.search(r"[A-Z]", compact))
    has_digit = bool(re.search(r"\d", compact))
    if strict:
        if len(compact) < 6:
            return False
        if not (has_digit and (has_alpha or len(compact) >= 8)):
            return False
    else:
        if len(compact) < 8:
            return False
        if not (has_alpha and has_digit):
            return False
    return True


def extract_receipt_entities(text: str) -> dict:
    src = safe_str(text)
    if not src:
        return {
            "amounts": [],
            "currencies": [],
            "dates": [],
            "times": [],
            "statuses": [],
            "operation_ids": [],
            "card_like": [],
            "account_like": [],
            "iban_like": [],
            "phone_like": [],
            "operation_labels_present": False,
            "transaction_context_present": False,
            "receipt_like_context_present": False,
        }

    amounts = [m.group(0).strip() for m in AMOUNT_PATTERN.finditer(src)]
    if not amounts:
        amounts = _extract_contextual_amount_candidates(src)
    currencies = _extract_currency_candidates(src)
    dates = DATE_PATTERN.findall(src)
    times = TIME_PATTERN.findall(src)
    statuses = [m.group(0).strip() for m in STATUS_PATTERN.finditer(src)]

    card_like = [m.group(0).strip() for m in CARD_MASK_PATTERN.finditer(src)]

    iban_like = []
    for token in re.findall(r"\b[A-Z]{2}\d{2}(?:[\s\-]?[A-Z0-9]){10,30}\b", src.upper()):
        if is_iban_like(token):
            iban_like.append(token)

    account_like = []
    for m in ACCOUNT_PATTERN.finditer(src):
        candidate = safe_str(m.group(1))
        if candidate:
            account_like.append(candidate)
    for token in re.findall(r"\b[A-Z0-9]{14,34}\b", src.upper()):
        if token.isdigit():
            continue
        if is_account_like(token):
            account_like.append(token)

    phone_like = []
    for m in PHONE_PATTERN.finditer(src):
        candidate = m.group(0).strip()
        if is_phone_like(candidate):
            phone_like.append(candidate)

    operation_ids = []
    operation_labels_present = False
    for m in OPERATION_ID_CAPTURE_PATTERN.finditer(src):
        operation_labels_present = True
        candidate = safe_str(m.group(1)).strip(":-# ")
        if not candidate:
            continue
        if _is_valid_operation_id_candidate(candidate, strict=True):
            operation_ids.append(candidate)

    # Консервативный fallback: id-подобные токены только в контекстных строках.
    for line in src.splitlines():
        if not TRANSACTION_CONTEXT_PATTERN.search(line):
            continue
        for token in re.findall(r"\b[A-Z0-9-]{8,32}\b", line.upper()):
            if _is_valid_operation_id_candidate(token, strict=False):
                operation_ids.append(token)

    # Исключаем дублирование operation_id с account/iban/card-like реквизитами.
    blocked_ids = {
        _normalize_compact(v)
        for v in [*iban_like, *account_like, *card_like]
        if _normalize_compact(v)
    }
    operation_ids = [
        v for v in operation_ids
        if _normalize_compact(v) and _normalize_compact(v) not in blocked_ids
    ]

    transaction_context_present = bool(TRANSACTION_CONTEXT_PATTERN.search(src))
    receipt_like_context_present = bool(re.search(r"\b(?:чек|receipt|квитан|invoice)\b", src, flags=re.IGNORECASE))

    return {
        "amounts": _unique_limited(amounts),
        "currencies": _unique_limited(currencies),
        "dates": _unique_limited(dates),
        "times": _unique_limited(times),
        "statuses": _unique_limited(statuses),
        "operation_ids": _unique_limited(operation_ids),
        "card_like": _unique_limited(card_like),
        "account_like": _unique_limited(account_like),
        "iban_like": _unique_limited(iban_like),
        "phone_like": _unique_limited(phone_like),
        "operation_labels_present": operation_labels_present,
        "transaction_context_present": transaction_context_present,
        "receipt_like_context_present": receipt_like_context_present,
    }


def build_critical_fields_summary(forensic_summary: dict, entities: dict) -> dict:
    summary = dict(forensic_summary or {})

    amount_candidates = entities.get("amounts", [])
    currency_candidates = entities.get("currencies", [])
    date_candidates = entities.get("dates", [])
    time_candidates = entities.get("times", [])
    status_candidates = entities.get("statuses", [])
    operation_id_candidates = entities.get("operation_ids", [])
    card_candidates = entities.get("card_like", [])
    account_candidates = entities.get("account_like", [])
    iban_candidates = entities.get("iban_like", [])
    phone_candidates = entities.get("phone_like", [])

    amount_found = bool(amount_candidates)
    currency_found = bool(currency_candidates)
    date_found = bool(date_candidates)
    time_found = bool(time_candidates)
    status_found = bool(status_candidates)
    operation_id_found = bool(operation_id_candidates)
    card_like_found = bool(card_candidates)
    account_like_found = bool(account_candidates)
    iban_like_found = bool(iban_candidates)
    phone_like_found = bool(phone_candidates)

    operation_id_too_short = False
    operation_id_too_generic = False
    if operation_id_candidates:
        compact_ids = [_normalize_compact(v) for v in operation_id_candidates]
        operation_id_too_short = all(len(v) < 8 for v in compact_ids if v)
        operation_id_too_generic = any(_is_generic_operation_id(v) for v in operation_id_candidates)

    core_supporting_fields_count = sum(
        int(v) for v in (
            currency_found,
            date_found,
            time_found,
            status_found,
            operation_id_found,
            bool(entities.get("transaction_context_present")),
        )
    )
    auxiliary_supporting_fields_count = sum(
        int(v) for v in (
            card_like_found,
            account_like_found,
            iban_like_found,
            phone_like_found,
        )
    )
    supporting_fields_count = core_supporting_fields_count + auxiliary_supporting_fields_count
    too_few_supporting_fields = amount_found and core_supporting_fields_count <= 1 and auxiliary_supporting_fields_count <= 1

    normalized_amounts = {_normalize_amount_candidate(v) for v in amount_candidates if _normalize_amount_candidate(v)}
    normalized_dates = {_normalize_date_candidate(v) for v in date_candidates if _normalize_date_candidate(v)}
    conflicting_amount_candidates = len(normalized_amounts) >= 2
    conflicting_date_candidates = len(normalized_dates) >= 2

    critical_fields_found_count = sum(
        int(v) for v in (
            amount_found,
            currency_found,
            date_found,
            time_found,
            status_found,
            operation_id_found,
            card_like_found,
            account_like_found,
            iban_like_found,
            phone_like_found,
        )
    )

    summary.update({
        "amount_found": amount_found,
        "currency_found": currency_found,
        "date_found": date_found,
        "time_found": time_found,
        "status_found": status_found,
        "operation_id_found": operation_id_found,
        "card_like_found": card_like_found,
        "account_like_found": account_like_found,
        "iban_like_found": iban_like_found,
        "phone_like_found": phone_like_found,
        "critical_fields_found_count": critical_fields_found_count,
        "amount_candidates_count": len(amount_candidates),
        "date_candidates_count": len(date_candidates),
        "time_candidates_count": len(time_candidates),
        "operation_id_candidates_count": len(operation_id_candidates),
        "operation_id_too_short": operation_id_too_short,
        "operation_id_too_generic": operation_id_too_generic,
        "too_few_supporting_fields": too_few_supporting_fields,
        "conflicting_amount_candidates": conflicting_amount_candidates,
        "conflicting_date_candidates": conflicting_date_candidates,
        "supporting_fields_count": supporting_fields_count,
        "core_supporting_fields_count": core_supporting_fields_count,
        "auxiliary_supporting_fields_count": auxiliary_supporting_fields_count,
        "transaction_context_present": bool(entities.get("transaction_context_present")),
        "receipt_like_context_present": bool(entities.get("receipt_like_context_present")),
        "operation_labels_present": bool(entities.get("operation_labels_present")),
    })
    return summary


def analyze_receipt_template_suspicion(text: str, entities: dict, critical_summary: dict, format_stats: dict) -> dict:
    score = 0
    signals = []

    amount_found = bool(critical_summary.get("amount_found"))
    date_found = bool(critical_summary.get("date_found"))
    status_found = bool(critical_summary.get("status_found"))
    operation_id_found = bool(critical_summary.get("operation_id_found"))
    core_supporting_fields_count = int(critical_summary.get("core_supporting_fields_count", 0) or 0)
    auxiliary_supporting_fields_count = int(critical_summary.get("auxiliary_supporting_fields_count", 0) or 0)
    critical_fields_found_count = int(critical_summary.get("critical_fields_found_count", 0) or 0)

    tx_core_signals = sum(
        int(v) for v in (
            critical_summary.get("currency_found"),
            date_found,
            critical_summary.get("time_found"),
            status_found,
            operation_id_found,
            critical_summary.get("transaction_context_present"),
        )
    )

    if critical_summary.get("too_few_supporting_fields"):
        score += 1
        signals.append("too_few_supporting_fields")

    if (amount_found or status_found or date_found) and tx_core_signals <= 1 and core_supporting_fields_count <= 1:
        score += 1
        signals.append("weak_transaction_context")

    if critical_summary.get("operation_id_too_short"):
        score += 1
        signals.append("operation_id_too_short")

    if critical_summary.get("operation_id_too_generic"):
        score += 1
        signals.append("operation_id_too_generic")

    if critical_summary.get("operation_labels_present") and not operation_id_found and (amount_found or date_found or status_found):
        score += 1
        signals.append("operation_label_without_value")

    if critical_summary.get("conflicting_amount_candidates"):
        score += 1
        signals.append("conflicting_amount_candidates")

    if critical_summary.get("conflicting_date_candidates"):
        score += 1
        signals.append("conflicting_date_candidates")

    if core_supporting_fields_count <= 1 and auxiliary_supporting_fields_count <= 1 and (amount_found or status_found):
        score += 1
        signals.append("low_semantic_depth")

    image_page_ratio = float(format_stats.get("image_page_ratio", 0.0) or 0.0)
    native_text_len = int(format_stats.get("native_text_length", 0) or 0)
    if image_page_ratio >= 0.5 and core_supporting_fields_count == 0 and auxiliary_supporting_fields_count <= 1 and native_text_len < 20:
        score += 1
        signals.append("image_low_context")

    text_norm = normalize_text_for_match(text)
    if ("чек" in text_norm or "receipt" in text_norm) and not entities.get("transaction_context_present") and core_supporting_fields_count == 0:
        score += 1
        signals.append("receipt_label_low_context")

    # Один слабый сигнал не должен резко повышать suspiciousness.
    if len(signals) <= 1:
        score = min(score, 1)
    elif len(signals) == 2:
        score = min(score, 2)
    score = min(score, 7)

    return {
        "score": score,
        "signals": signals[:6],
        "signals_count": len(signals),
    }


LIMITED_ANALYSIS_VERDICT_TEXT = (
    "⚠️ Не удалось надёжно проверить PDF, рекомендую запросить дополнительное подтверждение перевода "
    "(фото/видео/выписка) или проверить поступление"
)
SUSPICIOUS_RECEIPT_VERDICT_TEXT = (
    "⚠️ Чек выглядит подозрительно: структура или реквизиты нетипично слабые. "
    "Рекомендуется запросить дополнительное подтверждение перевода или проверить поступление"
)


def build_pdf_verdict(
    edit_score: int,
    template_score: int,
    receipt_format_type: str,
    critical_summary: dict,
    limitations: list[str],
) -> dict:
    reasons = []
    limitation_set = set(limitations or [])

    suspicious_critical_lines = int(critical_summary.get("suspicious_critical_lines_total", 0) or 0)
    core_supporting = int(critical_summary.get("core_supporting_fields_count", 0) or 0)
    critical_found = int(critical_summary.get("critical_fields_found_count", 0) or 0)
    operation_id_found = bool(critical_summary.get("operation_id_found"))
    transaction_context_present = bool(critical_summary.get("transaction_context_present"))
    too_few_supporting = bool(critical_summary.get("too_few_supporting_fields"))
    conflicting_amounts = bool(critical_summary.get("conflicting_amount_candidates"))
    conflicting_dates = bool(critical_summary.get("conflicting_date_candidates"))

    if edit_score >= 7:
        reasons.append("high_edit_score")
        return {
            "verdict_status": "edited",
            "verdict_text": "❌ Обнаружены признаки редактирования",
            "reasons": reasons,
        }
    # Сильная forensic-комбинация даже ниже основного порога.
    if edit_score >= 6 and suspicious_critical_lines >= 2:
        reasons.extend(["strong_forensic_combo", "high_edit_score"])
        return {
            "verdict_status": "edited",
            "verdict_text": "❌ Обнаружены признаки редактирования",
            "reasons": reasons,
        }

    if "analysis_error" in limitation_set or "pdf_too_large" in limitation_set:
        reasons.append("severe_limitation")
        return {
            "verdict_status": "inconclusive",
            "verdict_text": LIMITED_ANALYSIS_VERDICT_TEXT,
            "reasons": reasons,
        }

    quality_flags = {
        "limited_text_extraction",
        "native_text_unavailable",
        "ocr_not_available",
        "ocr_low_text",
    }
    quality_hits = len(limitation_set.intersection(quality_flags))
    semantic_weak = (
        core_supporting <= 1 or
        critical_found <= 3 or
        too_few_supporting or
        (not transaction_context_present and not operation_id_found)
    )
    has_conflicts = conflicting_amounts or conflicting_dates

    if quality_hits >= 2 and core_supporting <= 1:
        reasons.append("low_analysis_confidence")
        return {
            "verdict_status": "inconclusive",
            "verdict_text": LIMITED_ANALYSIS_VERDICT_TEXT,
            "reasons": reasons,
        }

    if (
        receipt_format_type in {"image_pdf", "mixed_pdf"} and
        core_supporting == 0 and
        not transaction_context_present and
        ("limited_text_extraction" in limitation_set or quality_hits >= 1)
    ):
        reasons.append("image_or_mixed_low_text_confidence")
        return {
            "verdict_status": "inconclusive",
            "verdict_text": LIMITED_ANALYSIS_VERDICT_TEXT,
            "reasons": reasons,
        }

    if "limited_text_extraction" in limitation_set and core_supporting == 0 and not transaction_context_present:
        reasons.append("insufficient_text_context")
        return {
            "verdict_status": "inconclusive",
            "verdict_text": LIMITED_ANALYSIS_VERDICT_TEXT,
            "reasons": reasons,
        }

    # Suspicious должен требовать комбинацию сигналов, а не один слабый индикатор.
    suspicious_combo = (
        template_score >= 5 and semantic_weak and (has_conflicts or critical_found <= 4 or not operation_id_found)
    )
    moderate_forensic_combo = (
        (edit_score >= 4 and (template_score >= 3 or has_conflicts)) or
        (edit_score >= 5 and semantic_weak)
    )
    suspicious_conflict_combo = (
        has_conflicts and core_supporting <= 2 and (template_score >= 3 or suspicious_critical_lines >= 1)
    )
    if (suspicious_combo or moderate_forensic_combo or suspicious_conflict_combo) and quality_hits <= 1:
        reasons.append("template_semantic_suspicion")
        return {
            "verdict_status": "suspicious",
            "verdict_text": SUSPICIOUS_RECEIPT_VERDICT_TEXT,
            "reasons": reasons,
        }

    # Clean только при достаточном покрытии и отсутствии заметных рисков.
    clean_ready = (
        quality_hits == 0 and
        core_supporting >= 3 and
        critical_found >= 5 and
        transaction_context_present and
        edit_score <= 2 and
        template_score <= 2 and
        suspicious_critical_lines == 0 and
        not too_few_supporting and
        not has_conflicts
    )
    if clean_ready:
        return {
            "verdict_status": "clean",
            "verdict_text": "✅ Признаков редактирования не обнаружено",
            "reasons": reasons,
        }

    reasons.append("insufficient_confidence_for_clean")
    return {
        "verdict_status": "inconclusive",
        "verdict_text": LIMITED_ANALYSIS_VERDICT_TEXT,
        "reasons": reasons,
    }


def _is_document_like_receipt_candidate(format_type: str, format_stats: dict, text: str) -> bool:
    pages_total = int(format_stats.get("pages_total", 0) or 0)
    pages_with_native_text = int(format_stats.get("pages_with_native_text", 0) or 0)
    pages_with_text_blocks = int(format_stats.get("pages_with_text_blocks", 0) or 0)
    pages_with_image_blocks = int(format_stats.get("pages_with_image_blocks", 0) or 0)
    native_text_len = int(format_stats.get("native_text_length", len(text.strip())) or 0)
    image_page_ratio = float(format_stats.get("image_page_ratio", 0.0) or 0.0)
    text_page_ratio = float(format_stats.get("text_page_ratio", 0.0) or 0.0)

    if pages_total <= 0 or pages_total > 10:
        return False

    # image_pdf: пропускаем только image-dominant документы небольшой длины.
    if format_type == "image_pdf":
        if pages_with_image_blocks == 0:
            return False
        if image_page_ratio < 0.60:
            return False
        return pages_total <= 3

    # mixed_pdf: нужен хотя бы минимальный текстовый/структурный сигнал + image presence.
    if format_type == "mixed_pdf":
        if pages_with_image_blocks == 0:
            return False
        if pages_with_text_blocks >= 1 and native_text_len >= 16:
            return True
        return image_page_ratio >= 0.50 and pages_with_native_text >= 1 and pages_total <= 4

    # weak text_pdf: не пропускаем по "техническому мусору".
    if format_type == "text_pdf":
        return native_text_len >= 24 and text_page_ratio >= 0.50 and pages_with_text_blocks >= 1

    return False


def is_pdf_receipt_like(file_path: str) -> bool:
    """
    Lightweight pre-check: verify PDF text has enough receipt/payment signals.
    No OCR, no external calls.
    """
    doc = None
    try:
        doc = fitz.open(file_path)
        native_text = collect_native_text(doc)
        text = native_text.lower()
        native_text_len = len(text.strip())
        format_type, format_stats = _detect_receipt_format_type(doc, native_text)
        hits, found_groups = _receipt_semantic_groups_hits(text) if text else (0, set())
        entities = extract_receipt_entities(text) if text else extract_receipt_entities("")

        core_semantic_hits = sum(
            int(v) for v in (
                bool(entities.get("amounts")),
                bool(entities.get("currencies")),
                bool(entities.get("dates")),
                bool(entities.get("times")),
                bool(entities.get("statuses")),
                bool(entities.get("operation_ids")),
                bool(entities.get("transaction_context_present")),
            )
        )
        has_amount_context = bool(entities.get("amounts")) and any(
            (
                bool(entities.get("dates")),
                bool(entities.get("times")),
                bool(entities.get("operation_ids")),
                bool(entities.get("transaction_context_present")),
                bool(entities.get("statuses")),
            )
        )
        is_document_like = _is_document_like_receipt_candidate(format_type, format_stats, text)

        if text and len(text) >= 20:
            # Strong rule: amount + one of core transactional context groups.
            if "amount" in found_groups and (
                "date_time" in found_groups or
                "receipt" in found_groups or
                "operation" in found_groups
            ):
                return True

            # Более строгий fallback: не только количество групп, но и транзакционная глубина.
            if hits >= 3 and core_semantic_hits >= 2 and (
                "amount" in found_groups or
                "operation" in found_groups or
                has_amount_context
            ):
                return True

        # text_pdf: допускаем мягче и в первую очередь смотрим на транзакционную семантику.
        # Здесь не делаем жесткий structural reject, чтобы не терять валидные чеки с нестандартной версткой.
        if format_type == "text_pdf":
            strong_semantic_accept = (
                core_semantic_hits >= 2 and
                (has_amount_context or "operation" in found_groups or "receipt" in found_groups)
            )
            if strong_semantic_accept:
                return True

            # Осторожный fallback для кривого text extraction:
            # требуем сумму + явный признак транзакционного/чекового контекста.
            has_amount = bool(entities.get("amounts")) or "amount" in found_groups
            has_strong_doc_context = (
                bool(entities.get("transaction_context_present")) or
                bool(entities.get("operation_ids")) or
                bool(entities.get("receipt_like_context_present")) or
                bool(entities.get("statuses")) or
                "operation" in found_groups or
                "receipt" in found_groups
            )

            return (
                has_amount and
                has_strong_doc_context and
                (hits >= 2 or core_semantic_hits >= 2)
            )

        # mixed_pdf: недостаточно "похожести на документ"; нужна хотя бы минимальная семантика.
        if format_type == "mixed_pdf":
            if is_document_like:
                if core_semantic_hits >= 2 and (has_amount_context or "operation" in found_groups):
                    return True
                if hits >= 3 and core_semantic_hits >= 1 and ("receipt" in found_groups or "operation" in found_groups):
                    return True

        # image_pdf: самый строгий fallback, чтобы не пропускать произвольные image-only PDF.
        # Разрешаем только при совокупности строгой структуры + хотя бы слабого транзакционного сигнала.
        if format_type == "image_pdf":
            if is_document_like:
                pages_total = int(format_stats.get("pages_total", 0) or 0)
                image_ratio = float(format_stats.get("image_page_ratio", 0.0) or 0.0)
                pages_with_text_blocks = int(format_stats.get("pages_with_text_blocks", 0) or 0)
                total_image_blocks = int(format_stats.get("total_image_blocks", 0) or 0)
                strict_image_structure = (
                    pages_total <= 2 and
                    image_ratio >= 0.85 and
                    pages_with_text_blocks == 0 and
                    1 <= total_image_blocks <= 6
                )
                if strict_image_structure and (
                    core_semantic_hits >= 1 and (
                        has_amount_context or
                        "operation" in found_groups or
                        "receipt" in found_groups
                    )
                ):
                    return True

        return False
    except Exception:
        logger.exception("Ошибка pre-check PDF")
        return False
    finally:
        try:
            if doc is not None:
                doc.close()
        except Exception:
            pass


def _dominant_value(values):
    values = [v for v in values if v is not None and v != ""]
    if not values:
        return None
    return Counter(values).most_common(1)[0][0]


def _size_suspicion(span_size: float, baseline_size: float | None) -> int:
    if not baseline_size or baseline_size <= 0 or span_size <= 0:
        return 0

    ratio = span_size / baseline_size
    if ratio <= 0.75 or ratio >= 1.30:
        return 2
    if ratio <= 0.85 or ratio >= 1.18:
        return 1
    return 0


def _count_intersections(target_bbox, spans) -> int:
    if not target_bbox:
        return 0
    hits = 0
    for other in spans:
        other_bbox = other.get("bbox")
        if not other_bbox or other_bbox == target_bbox:
            continue
        if intersects(target_bbox, other_bbox):
            hits += 1
    return hits


def _is_numeric_or_id_like(text: str) -> bool:
    return any(
        (
            is_amount_like(text),
            is_date_like(text),
            is_time_like(text),
            is_card_mask_like(text),
            is_operation_id_like(text),
            is_phone_like(text),
            is_iban_like(text),
            is_account_like(text),
        )
    )


def _is_short_insert_like(text: str) -> bool:
    compact = re.sub(r"\s+", "", safe_str(text))
    if not compact:
        return False
    if len(compact) <= 2:
        return True
    return len(compact) <= 3 and bool(re.fullmatch(r"[0-9A-Za-z]+", compact))


def _span_is_critical(span_text: str, line_text: str) -> bool:
    _ = line_text
    # Span-level scoring применяем в основном к самим значениям полей, а не к keyword-ярлыкам.
    return any(
        (
            is_amount_like(span_text),
            is_date_like(span_text),
            is_time_like(span_text),
            is_card_mask_like(span_text),
            is_operation_id_like(span_text),
            is_phone_like(span_text),
            is_iban_like(span_text),
            is_account_like(span_text),
        )
    )


def analyze_critical_fields(page) -> tuple[int, int, int]:
    """
    Критические поля: сумма/дата/время/ID/карта/телефон/IBAN/счет и линии с профильными keywords.
    Важно: телефон, IBAN, счет или редкий банк сами по себе не подозрительны.
    Score растет только при признаках редактирования: вставках, overlap, смешении стилей и т.п.
    """
    score = 0
    critical_lines = 0
    suspicious_critical_lines = 0

    try:
        page_dict = page.get_text("dict")
    except Exception:
        return 0, 0, 0

    for block in page_dict.get("blocks", []):
        if block.get("type") != 0:
            continue

        for line in block.get("lines", []):
            spans = []
            for span in line.get("spans", []):
                text = safe_str(span.get("text"))
                if not text:
                    continue
                spans.append({
                    "text": text,
                    "bbox": span.get("bbox"),
                    "font": safe_str(span.get("font")) or "Unknown",
                    "size": float(span.get("size", 0) or 0),
                    "color": span.get("color"),
                })

            if not spans:
                continue

            line_text = " ".join(s["text"] for s in spans)
            line_fonts = [s["font"] for s in spans]
            line_sizes = [s["size"] for s in spans if s["size"] > 0]
            line_colors = [s["color"] for s in spans]

            dominant_font = _dominant_value(line_fonts)
            dominant_color = _dominant_value(line_colors)
            baseline_size = median(line_sizes) if line_sizes else None
            line_is_critical = contains_critical_keyword(line_text) or any(
                _is_numeric_or_id_like(s["text"]) for s in spans
            )

            if line_is_critical:
                critical_lines += 1

            line_score = 0
            unique_fonts = {f for f in line_fonts if f}
            unique_colors = {c for c in line_colors if c is not None}
            has_style_anomaly = False
            if line_is_critical and len(unique_fonts) >= 2 and len(spans) <= 8:
                line_score += 1
                has_style_anomaly = True
            if line_is_critical and len(unique_colors) >= 2:
                line_score += 1
                has_style_anomaly = True
            if line_is_critical and line_sizes:
                if max(line_sizes) - min(line_sizes) >= 2.5:
                    line_score += 1
                    has_style_anomaly = True

            line_overlap_hits = 0
            for i in range(len(spans)):
                b1 = spans[i]["bbox"]
                if not b1:
                    continue
                for j in range(i + 1, len(spans)):
                    b2 = spans[j]["bbox"]
                    if not b2:
                        continue
                    if intersects(b1, b2) and spans[i]["text"] != spans[j]["text"]:
                        line_overlap_hits += 1
            if line_is_critical and line_overlap_hits >= 1:
                line_score += 2
                has_style_anomaly = True

            ordered_spans = sorted(
                [s for s in spans if s["bbox"]],
                key=lambda x: (x["bbox"][0], x["bbox"][1])
            )
            for idx, span in enumerate(ordered_spans):
                if not _is_short_insert_like(span["text"]):
                    continue
                near_critical = False
                if idx > 0 and _is_numeric_or_id_like(ordered_spans[idx - 1]["text"]):
                    near_critical = True
                if idx + 1 < len(ordered_spans) and _is_numeric_or_id_like(ordered_spans[idx + 1]["text"]):
                    near_critical = True
                # Короткие вставки учитываем только как вспомогательный сигнал при других аномалиях.
                if line_is_critical and near_critical and has_style_anomaly:
                    line_score += 1

            for span in spans:
                text = span["text"]
                if not _span_is_critical(text, line_text):
                    continue

                local_score = 0

                local_score += _size_suspicion(span["size"], baseline_size)

                if dominant_font and span["font"] != dominant_font and len(spans) >= 2:
                    local_score += 2

                if dominant_color is not None and span["color"] != dominant_color and len(spans) >= 2:
                    local_score += 1

                intersections = _count_intersections(span["bbox"], spans)
                if intersections >= 1:
                    local_score += 2

                if len(text) <= 12 and span["size"] > 0 and span["size"] < 7:
                    local_score += 1

                if _is_short_insert_like(text) and local_score >= 2:
                    local_score += 1

                if local_score >= 5:
                    score += 3
                    line_score += 2
                elif local_score >= 3:
                    score += 2
                    line_score += 1
                elif local_score >= 2:
                    score += 1

            if line_is_critical and line_score >= 3:
                suspicious_critical_lines += 1
                score += 1
            elif line_is_critical and line_score >= 2:
                score += 1

    return score, critical_lines, suspicious_critical_lines


def analyze_page_blocks(page) -> int:
    """
    Общий структурный анализ страницы.
    Более слабый, чем критический анализ суммы/даты.
    """
    score = 0

    try:
        page_dict = page.get_text("dict")
    except Exception:
        return 0

    span_records = []
    font_usage = {}
    font_sizes = []

    for block in page_dict.get("blocks", []):
        if block.get("type") != 0:
            continue

        for line in block.get("lines", []):
            for span in line.get("spans", []):
                text = safe_str(span.get("text"))
                if not text:
                    continue

                bbox = span.get("bbox")
                font = safe_str(span.get("font")) or "Unknown"
                size = float(span.get("size", 0) or 0)

                span_records.append({
                    "text": text,
                    "bbox": bbox,
                    "font": font,
                    "size": size,
                })

                font_usage[font] = font_usage.get(font, 0) + 1
                if size > 0:
                    font_sizes.append(size)

    if not span_records:
        return 0

    unique_fonts = len(font_usage)
    if unique_fonts >= 10:
        score += 2
    elif unique_fonts >= 8:
        score += 1

    if font_sizes:
        min_size = min(font_sizes)
        max_size = max(font_sizes)

        if min_size < 4.5:
            score += 1

        if max_size - min_size > 20:
            score += 1
        elif max_size - min_size > 12:
            score += 1

    overlap_hits = 0
    for i in range(len(span_records)):
        bbox1 = span_records[i]["bbox"]
        if not bbox1:
            continue
        for j in range(i + 1, len(span_records)):
            bbox2 = span_records[j]["bbox"]
            if not bbox2:
                continue

            if intersects(bbox1, bbox2):
                area1 = rect_area(bbox1)
                area2 = rect_area(bbox2)
                if area1 > 0 and area2 > 0:
                    t1 = span_records[i]["text"]
                    t2 = span_records[j]["text"]
                    if t1 != t2:
                        overlap_hits += 1
                        if overlap_hits >= 2:
                            score += 1
                            break
        if overlap_hits >= 5:
            score += 1

    suspicious_short = 0
    for block in page_dict.get("blocks", []):
        if block.get("type") != 0:
            continue
        for line in block.get("lines", []):
            line_spans = []
            line_text_parts = []
            for span in line.get("spans", []):
                text = safe_str(span.get("text"))
                if not text:
                    continue
                line_spans.append(span)
                line_text_parts.append(text)

            if not line_spans:
                continue
            line_text = " ".join(line_text_parts)
            if len(line_text) < 20:
                continue

            for span in line_spans:
                span_text = safe_str(span.get("text"))
                if _is_short_insert_like(span_text):
                    suspicious_short += 1
                    break

    if suspicious_short >= 4:
        score += 1

    return score


@dataclass
class PdfAnalysisResult:
    receipt_format_type: str
    format_stats: dict
    native_text: str
    effective_text: str
    edit_score: int
    template_suspicion_score: int
    critical_fields_summary: dict
    ocr_text: str = ""
    ocr_used: bool = False
    ocr_available: bool = False
    ocr_pages_used: int = 0
    ocr_text_length: int = 0
    ocr_pages_processed: int = 0
    ocr_pages_with_text: int = 0
    limitations: list[str] = field(default_factory=list)
    verdict_status: str = "inconclusive"
    verdict_reasons: list[str] = field(default_factory=list)
    verdict: str = "inconclusive"


def is_structured_pdf_receipt_candidate(result: PdfAnalysisResult) -> bool:
    if not result:
        return False

    limitations = set(result.limitations or [])
    if "analysis_error" in limitations or "pdf_too_large" in limitations:
        return False

    summary = result.critical_fields_summary or {}
    core_supporting = int(summary.get("core_supporting_fields_count", 0) or 0)
    critical_found = int(summary.get("critical_fields_found_count", 0) or 0)
    too_few_supporting = bool(summary.get("too_few_supporting_fields"))
    transaction_signal = any(
        (
            bool(summary.get("transaction_context_present")),
            bool(summary.get("operation_id_found")),
            bool(summary.get("receipt_like_context_present")),
        )
    )

    coverage_relaxed = not too_few_supporting
    if not coverage_relaxed:
        coverage_relaxed = (core_supporting >= 3) or (critical_found >= 6)

    if result.verdict_status == "clean" and coverage_relaxed and (
        core_supporting >= 2 or critical_found >= 4
    ):
        return True

    if core_supporting >= 2 and transaction_signal and coverage_relaxed:
        return True

    if critical_found >= 5 and core_supporting >= 2 and coverage_relaxed:
        return True

    return False


def _detect_receipt_format_type(doc: fitz.Document, native_text: str) -> tuple[str, dict]:
    pages_total = len(doc)
    pages_with_native_text = 0
    pages_with_text_blocks = 0
    pages_with_image_blocks = 0
    total_text_blocks = 0
    total_image_blocks = 0

    for page in doc:
        page_text = safe_str(page.get_text("text"))
        if page_text.strip():
            pages_with_native_text += 1

        try:
            page_dict = page.get_text("dict")
        except Exception:
            continue

        has_text_block = any(block.get("type") == 0 for block in page_dict.get("blocks", []))
        has_image_block = any(block.get("type") == 1 for block in page_dict.get("blocks", []))
        total_text_blocks += sum(1 for block in page_dict.get("blocks", []) if block.get("type") == 0)
        total_image_blocks += sum(1 for block in page_dict.get("blocks", []) if block.get("type") == 1)

        if has_text_block:
            pages_with_text_blocks += 1
        if has_image_block:
            pages_with_image_blocks += 1

    native_text_len = len(native_text.strip())
    text_page_ratio = (pages_with_native_text / pages_total) if pages_total else 0.0
    image_page_ratio = (pages_with_image_blocks / pages_total) if pages_total else 0.0

    confident_text_layer = (
        pages_total > 0 and
        native_text_len >= 40 and
        text_page_ratio >= 0.80 and
        pages_with_text_blocks >= max(1, round(pages_total * 0.70))
    )
    image_dominant = (
        pages_total > 0 and
        native_text_len < 20 and
        pages_with_native_text <= max(1, pages_total // 4) and
        pages_with_image_blocks >= max(1, (pages_total + 1) // 2)
    )

    if pages_total == 0:
        format_type = "mixed_pdf"
    elif confident_text_layer:
        format_type = "text_pdf"
    elif image_dominant:
        format_type = "image_pdf"
    else:
        format_type = "mixed_pdf"

    return format_type, {
        "pages_total": pages_total,
        "pages_with_native_text": pages_with_native_text,
        "pages_with_text_blocks": pages_with_text_blocks,
        "pages_with_image_blocks": pages_with_image_blocks,
        "total_text_blocks": total_text_blocks,
        "total_image_blocks": total_image_blocks,
        "has_native_text": bool(native_text.strip()),
        "native_text_length": native_text_len,
        "text_page_ratio": text_page_ratio,
        "image_page_ratio": image_page_ratio,
    }


def _default_ocr_result() -> dict:
    return {
        "ocr_text": "",
        "ocr_pages_used": 0,
        "ocr_pages_processed": 0,
        "ocr_pages_with_text": 0,
        "ocr_text_length": 0,
        "ocr_available": False,
        "ocr_used": False,
        "ocr_limitations": [],
    }


def extract_text_with_ocr(file_path: str, doc: fitz.Document, max_pages: int = 4) -> dict:
    _ = file_path
    result = _default_ocr_result()

    try:
        import pytesseract  # type: ignore
        from PIL import Image  # type: ignore
    except Exception:
        result["ocr_limitations"].append("ocr_not_available")
        return result

    try:
        _ = pytesseract.get_tesseract_version()
    except Exception:
        result["ocr_limitations"].append("ocr_not_available")
        return result

    result["ocr_available"] = True
    parts = []
    pages_processed = 0
    pages_with_text = 0
    max_pages = max(1, int(max_pages or 1))
    max_pages = min(len(doc), max_pages)
    if len(doc) > max_pages:
        result["ocr_limitations"].append("ocr_page_limit_applied")

    for idx, page in enumerate(doc):
        if idx >= max_pages:
            break
        try:
            page_native_text = safe_str(page.get_text("text"))
            native_len = len(page_native_text.strip())
            page_entities = extract_receipt_entities(page_native_text)
            core_hits = sum(
                int(v) for v in (
                    bool(page_entities.get("amounts")),
                    bool(page_entities.get("currencies")),
                    bool(page_entities.get("dates")),
                    bool(page_entities.get("times")),
                    bool(page_entities.get("statuses")),
                    bool(page_entities.get("operation_ids")),
                    bool(page_entities.get("transaction_context_present")),
                )
            )

            page_dict = page.get_text("dict")
            has_image_blocks = any(block.get("type") == 1 for block in page_dict.get("blocks", []))
            should_ocr_page = (
                native_len == 0 or
                native_len < 40 or
                (has_image_blocks and native_len < 120 and core_hits <= 1)
            )
            if not should_ocr_page:
                continue

            pix = page.get_pixmap(matrix=fitz.Matrix(2, 2), alpha=False)
            img = Image.open(io.BytesIO(pix.tobytes("png"))).convert("RGB")
            pages_processed += 1
            try:
                txt = safe_str(pytesseract.image_to_string(img, lang="rus+eng"))
            except Exception:
                txt = safe_str(pytesseract.image_to_string(img))

            txt = _cleanup_ocr_text(txt)
            if txt:
                pages_with_text += 1
                parts.append(txt)
        except Exception:
            continue

    ocr_text = "\n".join(parts).strip()
    result["ocr_text"] = ocr_text
    result["ocr_pages_used"] = pages_with_text
    result["ocr_pages_processed"] = pages_processed
    result["ocr_pages_with_text"] = pages_with_text
    result["ocr_text_length"] = len(ocr_text)
    result["ocr_used"] = pages_with_text > 0

    if result["ocr_used"] and result["ocr_text_length"] < 20:
        result["ocr_limitations"].append("ocr_low_text")
    return result


def _should_run_ocr(format_type: str, native_text: str, native_entities: dict, format_stats: dict) -> bool:
    native_len = len(safe_str(native_text).strip())
    if format_type == "image_pdf":
        return True

    tx_core_hits = sum(
        int(v) for v in (
            bool(native_entities.get("amounts")),
            bool(native_entities.get("currencies")),
            bool(native_entities.get("dates")),
            bool(native_entities.get("times")),
            bool(native_entities.get("statuses")),
            bool(native_entities.get("operation_ids")),
            bool(native_entities.get("transaction_context_present")),
        )
    )

    if native_len < 24:
        return True
    if format_type == "mixed_pdf" and (native_len < 100 or tx_core_hits <= 1):
        return True
    if format_type == "text_pdf" and native_len < 18 and tx_core_hits == 0:
        return True
    if format_type == "text_pdf" and native_len < 32 and tx_core_hits == 0 and not native_entities.get("receipt_like_context_present"):
        return True

    image_ratio = float(format_stats.get("image_page_ratio", 0.0) or 0.0)
    return format_type == "mixed_pdf" and image_ratio >= 0.6 and tx_core_hits <= 2


def _cleanup_ocr_text(text: str) -> str:
    lines = []
    for raw in safe_str(text).splitlines():
        line = re.sub(r"\s+", " ", raw).strip()
        if not line:
            continue
        if not re.search(r"[A-Za-zА-Яа-я0-9]", line):
            continue
        if len(line) <= 2:
            continue
        if len(line) < 5 and not re.search(r"\d", line):
            continue
        lines.append(line)
    return "\n".join(lines).strip()


def _build_effective_text(native_text: str, ocr_text: str = "") -> str:
    native = safe_str(native_text).strip()
    ocr = safe_str(ocr_text).strip()
    if native and not ocr:
        return native
    if ocr and not native:
        return ocr
    if not native and not ocr:
        return ""

    native_lines = [ln.strip() for ln in native.splitlines() if ln.strip()]
    ocr_lines = [ln.strip() for ln in ocr.splitlines() if ln.strip()]

    seen = set()
    merged = []
    for line in [*native_lines, *ocr_lines]:
        key = normalize_text_for_match(line)
        if not key or key in seen:
            continue
        seen.add(key)
        merged.append(line)

    return "\n".join(merged).strip()


def _analyze_template_suspicion(
    _doc: fitz.Document,
    _metadata: dict,
    _effective_text: str,
    _format_stats: dict,
    _entities: dict,
    _critical_summary: dict,
) -> dict:
    return analyze_receipt_template_suspicion(
        _effective_text,
        _entities,
        _critical_summary,
        _format_stats,
    )


def _build_limitations(
    format_type: str,
    native_text: str,
    effective_text: str,
    ocr_info: dict,
    ocr_needed: bool,
    entities: dict,
) -> list[str]:
    limitations = []
    native_len = len(safe_str(native_text).strip())
    effective_len = len(safe_str(effective_text).strip())
    if format_type == "image_pdf":
        limitations.append("image_based_pdf")
    if not native_text.strip():
        limitations.append("native_text_unavailable")
    semantic_depth = sum(
        int(v) for v in (
            bool(entities.get("amounts")),
            bool(entities.get("currencies")),
            bool(entities.get("dates")),
            bool(entities.get("times")),
            bool(entities.get("statuses")),
            bool(entities.get("operation_ids")),
            bool(entities.get("transaction_context_present")),
        )
    )

    # OCR-недоступность считаем значимой только когда действительно не хватает текста/семантики.
    weak_text_or_semantics = (effective_len < 36) or (semantic_depth <= 1)
    image_or_mixed_weak = format_type in {"image_pdf", "mixed_pdf"} and (effective_len < 60 or semantic_depth <= 2)
    if ocr_needed and not ocr_info.get("ocr_available", False) and (weak_text_or_semantics or image_or_mixed_weak):
        limitations.append("ocr_not_available")
    if ocr_info.get("ocr_used", False):
        limitations.append("ocr_used")

    for item in ocr_info.get("ocr_limitations", []):
        if item not in limitations:
            limitations.append(item)

    if effective_len < 24 or semantic_depth == 0:
        limitations.append("limited_text_extraction")
    return limitations


def analyze_pdf_structured(file_path: str) -> PdfAnalysisResult:
    """
    Более точный скоринг:
    сильные признаки:
      - modDate != creationDate
      - редактор в producer/creator
      - JS
      - embedded files
    средние:
      - multiple revisions
      - annotations/widgets
      - аномалии суммы/даты
    слабые:
      - общая странность структуры страницы
    """
    score = 0
    template_suspicion_score = 0
    native_text = ""
    effective_text = ""
    ocr_text = ""
    ocr_used = False
    ocr_available = False
    ocr_pages_used = 0
    ocr_text_length = 0
    ocr_pages_processed = 0
    ocr_pages_with_text = 0
    entities = {}
    receipt_format_type = "mixed_pdf"
    format_stats: dict = {}
    critical_summary = {
        "critical_lines_total": 0,
        "suspicious_critical_lines_total": 0,
        "critical_score": 0,
        "structural_score": 0,
        "update_markers": 0,
    }
    limitations: list[str] = []
    doc = None

    try:
        file_size = os.path.getsize(file_path)
        if file_size > MAX_PDF_SIZE_MB * 1024 * 1024:
            return PdfAnalysisResult(
                receipt_format_type=receipt_format_type,
                format_stats=format_stats,
                native_text=native_text,
                effective_text=effective_text,
                ocr_text=ocr_text,
                ocr_used=ocr_used,
                ocr_available=ocr_available,
                ocr_pages_used=ocr_pages_used,
                ocr_text_length=ocr_text_length,
                ocr_pages_processed=ocr_pages_processed,
                ocr_pages_with_text=ocr_pages_with_text,
                edit_score=score,
                template_suspicion_score=template_suspicion_score,
                critical_fields_summary=critical_summary,
                limitations=["pdf_too_large"],
                verdict_status="inconclusive",
                verdict_reasons=["pdf_too_large"],
                verdict=LIMITED_ANALYSIS_VERDICT_TEXT,
            )

        with open(file_path, "rb") as f:
            raw_bytes = f.read()

        doc = fitz.open(file_path)
        metadata = doc.metadata or {}
        native_text = collect_native_text(doc)
        receipt_format_type, format_stats = _detect_receipt_format_type(doc, native_text)
        native_entities = extract_receipt_entities(native_text)
        ocr_info = _default_ocr_result()
        ocr_needed = _should_run_ocr(receipt_format_type, native_text, native_entities, format_stats)
        if ocr_needed:
            ocr_info = extract_text_with_ocr(file_path, doc)

        ocr_text = safe_str(ocr_info.get("ocr_text"))
        ocr_used = bool(ocr_info.get("ocr_used", False))
        ocr_available = bool(ocr_info.get("ocr_available", False))
        ocr_pages_used = int(ocr_info.get("ocr_pages_used", 0) or 0)
        ocr_text_length = int(ocr_info.get("ocr_text_length", 0) or 0)
        ocr_pages_processed = int(ocr_info.get("ocr_pages_processed", 0) or 0)
        ocr_pages_with_text = int(ocr_info.get("ocr_pages_with_text", 0) or 0)

        effective_text = _build_effective_text(native_text, ocr_text)
        entities = extract_receipt_entities(effective_text)
        limitations = _build_limitations(
            receipt_format_type,
            native_text,
            effective_text,
            ocr_info,
            ocr_needed=ocr_needed,
            entities=entities,
        )

        creation_date = safe_str(metadata.get("creationDate"))
        mod_date = safe_str(metadata.get("modDate"))

        # Сильный признак
        if creation_date and mod_date and creation_date != mod_date:
            score += 4
        elif not creation_date and mod_date:
            score += 2

        # Сильный признак
        if detect_editor_hints(metadata):
            score += 3

        # Средний/сильный признак
        update_markers = count_incremental_updates(raw_bytes)
        critical_summary["update_markers"] = update_markers
        if update_markers >= 6:
            score += 3
        elif update_markers >= 4:
            score += 2

        has_annotations = False
        has_widgets = False

        for page in doc:
            if page.first_annot is not None:
                has_annotations = True

            widgets = list(page.widgets() or [])
            if widgets:
                has_widgets = True

        if has_annotations:
            score += 1

        if has_widgets:
            score += 1

        # Сильный признак
        try:
            emb_count = doc.embfile_count()
            if emb_count > 0:
                score += 3
        except Exception:
            pass

        # Сильный признак
        try:
            raw_text = raw_bytes.decode("latin-1", errors="ignore")
            if "/JavaScript" in raw_text or "/JS" in raw_text:
                score += 4
        except Exception:
            pass

        if native_text.strip():
            critical_score = 0
            structural_score = 0
            critical_lines_total = 0
            suspicious_critical_lines_total = 0

            for page in doc:
                page_score, page_critical_lines, page_suspicious_critical = analyze_critical_fields(page)
                critical_score += page_score
                critical_lines_total += page_critical_lines
                suspicious_critical_lines_total += page_suspicious_critical
                structural_score += analyze_page_blocks(page)

            score += critical_score
            score += min(structural_score, 2)

            # Легкое усиление только при повторяемых аномалиях в критических строках.
            if suspicious_critical_lines_total >= 2:
                score += 2
            elif suspicious_critical_lines_total == 1:
                score += 1

            critical_summary["critical_score"] = critical_score
            critical_summary["structural_score"] = structural_score
            critical_summary["critical_lines_total"] = critical_lines_total
            critical_summary["suspicious_critical_lines_total"] = suspicious_critical_lines_total

            logger.info(
                "PDF critical lines total=%s suspicious=%s file=%s",
                critical_lines_total,
                suspicious_critical_lines_total,
                os.path.basename(file_path),
            )

        critical_summary = build_critical_fields_summary(critical_summary, entities)
        critical_summary["ocr_used"] = ocr_used
        critical_summary["ocr_available"] = ocr_available
        critical_summary["ocr_text_length"] = ocr_text_length
        critical_summary["ocr_pages_used"] = ocr_pages_used
        critical_summary["ocr_pages_processed"] = ocr_pages_processed
        critical_summary["ocr_pages_with_text"] = ocr_pages_with_text
        template_eval = _analyze_template_suspicion(
            doc,
            metadata,
            effective_text,
            format_stats,
            entities,
            critical_summary,
        )
        template_suspicion_score = int(template_eval.get("score", 0) or 0)
        critical_summary["template_signals"] = template_eval.get("signals", [])
        critical_summary["template_signals_count"] = int(template_eval.get("signals_count", 0) or 0)

        verdict_info = build_pdf_verdict(
            edit_score=score,
            template_score=template_suspicion_score,
            receipt_format_type=receipt_format_type,
            critical_summary=critical_summary,
            limitations=limitations,
        )
        verdict_status = verdict_info["verdict_status"]
        verdict_reasons = verdict_info["reasons"]
        verdict = verdict_info["verdict_text"]

        logger.info(
            "PDF final verdict=%s reasons=%s edit_score=%s template_score=%s core_supporting=%s critical_found=%s suspicious_critical_lines=%s too_few_supporting=%s conflicting_amount=%s conflicting_date=%s operation_id_found=%s tx_context=%s format=%s native_len=%s ocr_used=%s ocr_len=%s ocr_processed=%s ocr_with_text=%s limitations=%s file=%s",
            verdict_status,
            ",".join(verdict_reasons[:5]) if verdict_reasons else "-",
            score,
            template_suspicion_score,
            int(critical_summary.get("core_supporting_fields_count", 0) or 0),
            int(critical_summary.get("critical_fields_found_count", 0) or 0),
            int(critical_summary.get("suspicious_critical_lines_total", 0) or 0),
            int(bool(critical_summary.get("too_few_supporting_fields"))),
            int(bool(critical_summary.get("conflicting_amount_candidates"))),
            int(bool(critical_summary.get("conflicting_date_candidates"))),
            int(bool(critical_summary.get("operation_id_found"))),
            int(bool(critical_summary.get("transaction_context_present"))),
            receipt_format_type,
            len(native_text),
            int(ocr_used),
            ocr_text_length,
            ocr_pages_processed,
            ocr_pages_with_text,
            ",".join(limitations[:4]),
            os.path.basename(file_path),
        )

        return PdfAnalysisResult(
            receipt_format_type=receipt_format_type,
            format_stats=format_stats,
            native_text=native_text,
            effective_text=effective_text,
            ocr_text=ocr_text,
            ocr_used=ocr_used,
            ocr_available=ocr_available,
            ocr_pages_used=ocr_pages_used,
            ocr_text_length=ocr_text_length,
            ocr_pages_processed=ocr_pages_processed,
            ocr_pages_with_text=ocr_pages_with_text,
            edit_score=score,
            template_suspicion_score=template_suspicion_score,
            critical_fields_summary=critical_summary,
            limitations=limitations,
            verdict_status=verdict_status,
            verdict_reasons=verdict_reasons,
            verdict=verdict,
        )

    except Exception:
        logger.exception("Ошибка обработки PDF")
        return PdfAnalysisResult(
            receipt_format_type=receipt_format_type,
            format_stats=format_stats,
            native_text=native_text,
            effective_text=effective_text,
            ocr_text=ocr_text,
            ocr_used=ocr_used,
            ocr_available=ocr_available,
            ocr_pages_used=ocr_pages_used,
            ocr_text_length=ocr_text_length,
            ocr_pages_processed=ocr_pages_processed,
            ocr_pages_with_text=ocr_pages_with_text,
            edit_score=score,
            template_suspicion_score=template_suspicion_score,
            critical_fields_summary=critical_summary,
            limitations=limitations + ["analysis_error"],
            verdict_status="inconclusive",
            verdict_reasons=["analysis_error"],
            verdict=LIMITED_ANALYSIS_VERDICT_TEXT,
        )
    finally:
        try:
            if doc is not None:
                doc.close()
        except Exception:
            pass


def analyze_pdf(file_path: str) -> str:
    result = analyze_pdf_structured(file_path)
    return result.verdict or LIMITED_ANALYSIS_VERDICT_TEXT


# =========================
# Handlers
# =========================
async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    if not user or not update.message:
        return

    set_mode(context, MODE_CARDS)
    await ensure_user_exists(user.id, user.username)

    start_text = update.message.text or ""
    referral_user_id = parse_start_referral(start_text)
    if referral_user_id and referral_user_id != user.id:
        await bind_referral(user.id, referral_user_id)

    fire_and_forget(asyncio.create_task(track_event_bg(user.id, user.username, "start")))

    access_text = await build_receipt_access_text(user.id, context.bot)

    await update.message.reply_text(
        "🔍 Привет!\n\n"
        "Выбери режим ниже:\n"
        "💳 <b>Проверка карт</b> — доступна всегда\n"
        "🧾 <b>Проверка чеков</b> — по доступам\n\n"
        f"{access_text}\n\n"
        "Сейчас активен режим: <b>Проверка карт</b>.\n"
        "Отправь 6 цифр BIN или полный номер карты.",
        parse_mode="HTML",
        reply_markup=build_menu(is_admin_user(update), get_mode(context))
    )


async def stats_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin_user(update) or not update.message:
        return
    text = await get_stats_text()
    await update.message.reply_text(
        text,
        parse_mode="HTML",
        reply_markup=build_menu(True, get_mode(context))
    )


async def grant_unlimited_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin_user(update) or not update.message:
        return

    if not context.args:
        await update.message.reply_text(
            "Использование: /grant_unlimited <user_id> [days]",
            reply_markup=build_menu(True, get_mode(context))
        )
        return

    try:
        target_user_id = int(context.args[0])
        days = int(context.args[1]) if len(context.args) > 1 else UNLIMITED_PLAN_DAYS
        if target_user_id <= 0 or days <= 0:
            raise ValueError
    except ValueError:
        await update.message.reply_text(
            "❌ Некорректные аргументы. Использование: /grant_unlimited <user_id> [days]",
            reply_markup=build_menu(True, get_mode(context))
        )
        return

    try:
        await grant_unlimited_access(
            target_user_id,
            days,
            plan_name="manual_unlimited",
            source="usdt_manual"
        )
        access_status = await get_user_receipt_access_status(target_user_id)
        until_text = format_access_until(access_status["unlimited_until"])

        await update.message.reply_text(
            f"✅ Безлимит выдан пользователю {target_user_id} на {days} дней.\n"
            f"Доступ до: {until_text}",
            reply_markup=build_menu(True, get_mode(context))
        )

        try:
            await context.bot.send_message(
                chat_id=target_user_id,
                text=f"⭐ Вам активирован безлимит на проверки чеков до {until_text}"
            )
        except Exception:
            logger.exception("Не удалось уведомить пользователя user_id=%s о выдаче безлимита", target_user_id)
    except Exception:
        logger.exception("Ошибка в /grant_unlimited")
        await update.message.reply_text(
            "❌ Не удалось выдать безлимит. Проверь аргументы и попробуй снова.",
            reply_markup=build_menu(True, get_mode(context))
        )


async def user_access_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin_user(update) or not update.message:
        return

    if not context.args:
        await update.message.reply_text(
            "Использование: /user_access <user_id>",
            reply_markup=build_menu(True, get_mode(context))
        )
        return

    try:
        target_user_id = int(context.args[0])
        if target_user_id <= 0:
            raise ValueError
    except ValueError:
        await update.message.reply_text(
            "❌ Некорректный user_id. Использование: /user_access <user_id>",
            reply_markup=build_menu(True, get_mode(context))
        )
        return

    row = await get_user_state(target_user_id)
    if row is None:
        await update.message.reply_text(
            f"Пользователь {target_user_id} не найден.",
            reply_markup=build_menu(True, get_mode(context))
        )
        return

    unlimited_until_raw = row["unlimited_until"]
    unlimited_until_text = format_access_until(unlimited_until_raw) if unlimited_until_raw else "—"

    await update.message.reply_text(
        "👤 <b>Доступ пользователя</b>\n\n"
        f"ID: <code>{target_user_id}</code>\n"
        f"🧾 receipt_quota: {int(row['receipt_quota'])}\n"
        f"♾️ unlimited_until: {unlimited_until_text}\n"
        f"💳 paid_plan: {row['paid_plan'] or '—'}\n"
        f"🔗 paid_source: {row['paid_source'] or '—'}\n"
        f"👥 invited_by: {row['invited_by'] if row['invited_by'] is not None else '—'}\n"
        f"✅ referrals_total: {int(row['referrals_total'])}\n"
        f"🎁 referral_reward_total: {int(row['referral_reward_total'])}",
        parse_mode="HTML",
        reply_markup=build_menu(True, get_mode(context))
    )


async def broadcast_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin_user(update) or not update.message:
        return
    context.user_data["awaiting_broadcast"] = True
    await update.message.reply_text(
        "📣 Пришли текстовое сообщение, которое нужно разослать всем пользователям.\n"
        "Отмена: /cancel",
        reply_markup=build_menu(True, get_mode(context))
    )


async def cancel_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin_user(update) or not update.message:
        return
    context.user_data.pop("awaiting_broadcast", None)
    context.user_data.pop("awaiting_admin_unlimited_username", None)
    await update.message.reply_text(
        "✅ Отменено.",
        reply_markup=build_menu(True, get_mode(context))
    )


async def do_broadcast(update: Update, context: ContextTypes.DEFAULT_TYPE):
    rows = await db_fetchall("SELECT user_id FROM users")
    user_ids = [int(r["user_id"]) for r in rows]

    sent = 0
    failed = 0

    admin_chat_id = update.effective_chat.id
    src_chat_id = update.effective_chat.id
    src_msg_id = update.message.message_id

    await update.message.reply_text(f"🚀 Старт рассылки. Получателей: {len(user_ids)}")

    for uid in user_ids:
        try:
            await context.bot.copy_message(
                chat_id=uid,
                from_chat_id=src_chat_id,
                message_id=src_msg_id
            )
            sent += 1
        except Exception:
            failed += 1

        if (sent + failed) % 25 == 0:
            await asyncio.sleep(1)

    await context.bot.send_message(
        chat_id=admin_chat_id,
        text=f"✅ Рассылка завершена.\nОтправлено: {sent}\nОшибок: {failed}"
    )


async def flag_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    if not query:
        return

    await query.answer()

    data = query.data or ""
    user_id = query.from_user.id

    if data.startswith("flag:"):
        h = data.split(":", 1)[1]
        kb = InlineKeyboardMarkup([[
            InlineKeyboardButton("✅ Да", callback_data=f"flag_yes:{h}"),
            InlineKeyboardButton("❌ Нет", callback_data=f"flag_no:{h}"),
        ]])
        await query.edit_message_reply_markup(reply_markup=kb)
        return

    if data.startswith("flag_yes:"):
        h = data.split(":", 1)[1]
        await set_pan_flag(h, user_id=user_id, is_problem=True)
        await query.edit_message_reply_markup(reply_markup=None)
        await query.message.reply_text("✅ Готово. Карта отмечена как проблемная.")
        return

    if data.startswith("flag_no:"):
        await query.edit_message_reply_markup(reply_markup=None)
        await query.message.reply_text("Ок, не отмечаю.")
        return


async def switch_mode(update: Update, context: ContextTypes.DEFAULT_TYPE, mode: str):
    set_mode(context, mode)
    if not update.message:
        return

    if mode == MODE_CARDS:
        await update.message.reply_text(
            "✅ Режим переключён: <b>Проверка карт</b>\n\n"
            "Отправь 6 цифр BIN или полный номер карты.",
            parse_mode="HTML",
            reply_markup=build_menu(is_admin_user(update), get_mode(context))
        )
    else:
        user = update.effective_user
        access_text = ""
        if user:
            access_text = await build_receipt_access_text(user.id, context.bot)
        await update.message.reply_text(
            "✅ Режим переключён: <b>Проверка чеков</b>\n\n"
            f"{access_text}\n\n"
            "Отправь PDF-файл чека.",
            parse_mode="HTML",
            reply_markup=build_menu(is_admin_user(update), get_mode(context))
        )


async def handle_card_flow(update: Update, context: ContextTypes.DEFAULT_TYPE, text_raw: str):
    user = update.effective_user
    if not user or not update.message:
        return

    await ensure_user_exists(user.id, user.username)
    digits = "".join(ch for ch in text_raw if ch.isdigit())

    if len(digits) < 6:
        await update.message.reply_text(
            "❌ В режиме <b>Проверка карт</b> нужно отправить 6 цифр BIN или полный номер карты.\n\n"
            "Для PDF-чека переключись на <b>Проверка чеков</b>.",
            parse_mode="HTML",
            reply_markup=build_menu(is_admin_user(update), get_mode(context))
        )
        return

    fire_and_forget(asyncio.create_task(track_event_bg(user.id, user.username, "card_request")))

    is_full_pan = len(digits) >= 12

    bin_code = digits[:6]
    brand = get_card_scheme(bin_code)
    issuer = "Unknown"
    country = "Unknown"

    local_row = bin_db.get(bin_code)
    if local_row is not None:
        _, issuer_local, country_local = local_row
        issuer = issuer_local
        country = country_local
    else:
        issuer, country = await fetch_binlist_info(bin_code)

    extra = ""
    reply_markup_inline = None

    if is_full_pan:
        h = pan_to_hash(digits)
        cnt, is_problem = await get_pan_info_and_inc(h)

        problem_line = "\n⚠️ <b>Метка</b>: карта отмечена как проблемная" if is_problem else ""
        extra = f"\n\n🔁 <b>Запросов по этому номеру</b>: {cnt}{problem_line}"

        reply_markup_inline = InlineKeyboardMarkup([[
            InlineKeyboardButton("🚩 Отметить карту как проблемную", callback_data=f"flag:{h}")
        ]])

    await update.message.reply_text(
        f"💳 <b>Платёжная система</b>: {brand}\n"
        f"🏦 <b>Банк</b>: {issuer}\n"
        f"🌍 <b>Страна</b>: {country}"
        f"{extra}",
        parse_mode="HTML",
        reply_markup=reply_markup_inline
    )

    inviter_user_id = await mark_referral_qualified_and_reward(user.id)
    if inviter_user_id:
        await notify_inviter_reward(context.bot, inviter_user_id, REFERRAL_REWARD_AMOUNT)


async def handle_receipt_flow(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    if not user or not update.message or not update.message.document:
        return
    await ensure_user_exists(user.id, user.username)

    document = update.message.document
    file_name = document.file_name or ""
    mime_type = document.mime_type or ""
    file_size = document.file_size or 0

    is_pdf = file_name.lower().endswith(".pdf") or mime_type == "application/pdf"

    if not is_pdf:
        await update.message.reply_text(
            "❌ В режиме <b>Проверка чеков</b> нужно отправить именно PDF-файл.\n\n"
            "Для BIN/карты переключись на <b>Проверка карт</b>.",
            parse_mode="HTML",
            reply_markup=build_menu(is_admin_user(update), get_mode(context))
        )
        return

    if file_size > MAX_PDF_SIZE_MB * 1024 * 1024:
        await update.message.reply_text(
            f"❌ PDF слишком большой. Отправь файл до {MAX_PDF_SIZE_MB} MB.",
            reply_markup=build_menu(is_admin_user(update), get_mode(context))
        )
        return

    tmp_path = None
    status = None
    access = None
    prefetched_result = None
    try:
        tg_file = await context.bot.get_file(document.file_id)
        with tempfile.NamedTemporaryFile(delete=False, suffix=".pdf") as tmp:
            tmp_path = tmp.name

        await tg_file.download_to_drive(custom_path=tmp_path)
        status = await update.message.reply_text("⏳ Проверяю PDF...")

        if not is_pdf_receipt_like(tmp_path):
            prefetched_result = analyze_pdf_structured(tmp_path)
            if not is_structured_pdf_receipt_candidate(prefetched_result):
                summary = prefetched_result.critical_fields_summary or {}
                logger.info(
                    "PDF precheck failed and structured fallback rejected verdict=%s core_supporting=%s critical_found=%s file=%s",
                    prefetched_result.verdict_status,
                    int(summary.get("core_supporting_fields_count", 0) or 0),
                    int(summary.get("critical_fields_found_count", 0) or 0),
                    os.path.basename(tmp_path),
                )
                await status.edit_text(
                    "❌ Не удалось распознать файл как PDF-чек.\n"
                    "Отправь платёжный чек в формате PDF.",
                    reply_markup=build_menu(is_admin_user(update), get_mode(context))
                )
                return
            summary = prefetched_result.critical_fields_summary or {}
            logger.info(
                "PDF precheck failed but structured fallback accepted verdict=%s core_supporting=%s critical_found=%s file=%s",
                prefetched_result.verdict_status,
                int(summary.get("core_supporting_fields_count", 0) or 0),
                int(summary.get("critical_fields_found_count", 0) or 0),
                os.path.basename(tmp_path),
            )

        # Invariant: non-PDF and oversized files never consume quota.
        # Pre-check runs before consume; quota is consumed only for valid receipt-like PDFs.
        access = await consume_receipt_access(user.id)
        if not access["allowed"]:
            await status.edit_text(
                await build_no_receipt_access_text(user.id, context.bot),
                parse_mode="HTML",
                reply_markup=build_menu(is_admin_user(update), get_mode(context))
            )
            return

        fire_and_forget(asyncio.create_task(track_event_bg(user.id, user.username, "receipt_request")))
        result = prefetched_result or analyze_pdf_structured(tmp_path)
        inviter_user_id = await mark_referral_qualified_and_reward(user.id)

        await status.edit_text(
            render_pdf_result_message(result, access),
            parse_mode="HTML"
        )

        if inviter_user_id:
            await notify_inviter_reward(context.bot, inviter_user_id, REFERRAL_REWARD_AMOUNT)
    except Exception:
        logger.exception("Ошибка проверки PDF")
        await refund_receipt_access(user.id, access)
        err_text = "❌ Не удалось проверить PDF. Попробуй ещё раз."
        if status is not None:
            await status.edit_text(err_text)
        else:
            await update.message.reply_text(
                err_text,
                reply_markup=build_menu(is_admin_user(update), get_mode(context))
            )
    finally:
        try:
            if tmp_path and os.path.exists(tmp_path):
                os.remove(tmp_path)
        except Exception:
            logger.exception("Не удалось удалить временный PDF")


async def handle_document(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message or not update.message.document:
        return

    mode = get_mode(context)

    if mode == MODE_CARDS:
        await update.message.reply_text(
            "❌ Сейчас активен режим <b>Проверка карт</b>.\n\n"
            "Отправь 6 цифр BIN или полный номер карты.\n"
            "Либо переключись на <b>Проверка чеков</b> и отправь PDF.",
            parse_mode="HTML",
            reply_markup=build_menu(is_admin_user(update), mode)
        )
        return

    await handle_receipt_flow(update, context)


async def handle_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    if not user or not update.message:
        return

    text_raw = (update.message.text or "").strip()
    mode = get_mode(context)

    if is_admin_user(update) and context.user_data.get("awaiting_broadcast"):
        admin_service_buttons = {
            BTN_ADMIN_PANEL,
            BTN_ADMIN_GRANT_30D,
            BTN_ADMIN_STATS,
            BTN_ADMIN_BROADCAST,
            BTN_ADMIN_BACK,
            "📊 Статистика",
            "📣 Рассылка",
        }
        if text_raw in admin_service_buttons:
            context.user_data["awaiting_broadcast"] = False
        else:
            context.user_data["awaiting_broadcast"] = False
            await do_broadcast(update, context)
            return

    if is_admin_user(update) and context.user_data.get("awaiting_admin_unlimited_username"):
        if text_raw == BTN_ADMIN_BACK:
            context.user_data.pop("awaiting_admin_unlimited_username", None)
            await update.message.reply_text(
                "🏠 Возврат в главное меню.",
                reply_markup=build_menu(True, mode)
            )
            return

        normalized_username = normalize_username_input(text_raw)
        if not normalized_username:
            await update.message.reply_text(
                "❌ Некорректный username.\n"
                "Отправь @username (латиница/цифры/underscore), например: @example_user",
                reply_markup=build_admin_menu()
            )
            return

        target_user_id = await find_user_id_by_username(normalized_username)
        if target_user_id is None:
            await update.message.reply_text(
                "❌ Пользователь не найден в базе.\n"
                "Попроси пользователя хотя бы один раз запустить бота через /start, затем попробуй снова.",
                reply_markup=build_admin_menu()
            )
            return

        try:
            await grant_unlimited_access(
                target_user_id,
                UNLIMITED_PLAN_DAYS,
                plan_name="manual_unlimited",
                source="admin_username_ui"
            )
            access_status = await get_user_receipt_access_status(target_user_id)
            until_text = format_access_until(access_status["unlimited_until"])
            context.user_data.pop("awaiting_admin_unlimited_username", None)

            await update.message.reply_text(
                "✅ Безлимит выдан.\n\n"
                f"👤 Username: @{normalized_username}\n"
                f"🆔 User ID: <code>{target_user_id}</code>\n"
                f"📅 Доступ до: {until_text}",
                parse_mode="HTML",
                reply_markup=build_admin_menu()
            )

            try:
                await context.bot.send_message(
                    chat_id=target_user_id,
                    text=f"⭐ Вам активирован безлимит на проверки чеков до {until_text}"
                )
            except Exception:
                logger.exception("Не удалось уведомить пользователя user_id=%s о выдаче безлимита через admin UI", target_user_id)
        except Exception:
            logger.exception("Ошибка выдачи безлимита через admin username UI")
            await update.message.reply_text(
                "❌ Не удалось выдать безлимит. Попробуй ещё раз.",
                reply_markup=build_admin_menu()
            )
        return

    if is_cards_button(text_raw):
        await switch_mode(update, context, MODE_CARDS)
        return

    if is_receipts_button(text_raw):
        await switch_mode(update, context, MODE_RECEIPTS)
        return

    if text_raw == "📚 Помощь":
        await update.message.reply_text(
            get_support_text(mode),
            parse_mode="HTML",
            reply_markup=SUPPORT_KB
        )
        return

    if text_raw == BTN_INVITE:
        await update.message.reply_text(
            await build_invite_text(user.id, context.bot),
            parse_mode="HTML",
            reply_markup=build_menu(is_admin_user(update), mode)
        )
        return

    if text_raw == BTN_ACCESS:
        access_text = await build_receipt_access_text(user.id, context.bot)
        offer_text = "\n".join(build_unlimited_offer_lines())
        await update.message.reply_text(
            f"⭐ <b>Статус доступа</b>\n\n{access_text}\n\n{offer_text}",
            parse_mode="HTML",
            reply_markup=build_menu(is_admin_user(update), mode)
        )
        return

    if text_raw == "📈 Курс Rapira":
        rate = await fetch_rapira_usdt_rub()
        if not rate:
            await update.message.reply_text(
                "❌ Не удалось получить курс Rapira сейчас. Попробуй позже.",
                reply_markup=build_menu(is_admin_user(update), mode)
            )
            return

        bid_ = rate.get("bidPrice")
        ask_ = rate.get("askPrice")
        close_ = rate.get("close")

        await update.message.reply_text(
            "📈 <b>Rapira USDT/RUB</b>\n"
            f"🟢 <b>Покупка</b>: {bid_}\n"
            f"🔴 <b>Продажа</b>: {ask_}\n"
            f"🔸 <b>Последняя цена</b>: {close_}\n\n"
            "Источник: Rapira Market Rates API",
            parse_mode="HTML",
            reply_markup=build_menu(is_admin_user(update), mode)
        )
        return

    if text_raw == "📊 Статистика" and is_admin_user(update):
        await stats_cmd(update, context)
        return

    if text_raw == "📣 Рассылка" and is_admin_user(update):
        await broadcast_cmd(update, context)
        return

    if text_raw == BTN_ADMIN_PANEL and is_admin_user(update):
        context.user_data.pop("awaiting_broadcast", None)
        context.user_data.pop("awaiting_admin_unlimited_username", None)
        await update.message.reply_text(
            "🛠 Админка\n\nВыбери действие:",
            reply_markup=build_admin_menu()
        )
        return

    if text_raw == BTN_ADMIN_GRANT_30D and is_admin_user(update):
        context.user_data.pop("awaiting_broadcast", None)
        context.user_data["awaiting_admin_unlimited_username"] = True
        await update.message.reply_text(
            "Отправь @username пользователя, которому нужно выдать безлимит на 30 дней.\n"
            "Пользователь должен уже хотя бы раз запустить бота.",
            reply_markup=build_admin_menu()
        )
        return

    if text_raw == BTN_ADMIN_BACK and is_admin_user(update):
        context.user_data.pop("awaiting_broadcast", None)
        context.user_data.pop("awaiting_admin_unlimited_username", None)
        await update.message.reply_text(
            "🏠 Возврат в главное меню.",
            reply_markup=build_menu(True, mode)
        )
        return

    digits = "".join(ch for ch in text_raw if ch.isdigit())

    if mode == MODE_CARDS:
        if len(digits) == 0:
            await update.message.reply_text(
                "💳 Отправь 6 цифр BIN или полный номер карты.",
                reply_markup=build_menu(is_admin_user(update), mode)
            )
            return
        await handle_card_flow(update, context, text_raw)
        return

    if len(digits) >= 6:
        await update.message.reply_text(
            "❌ Сейчас активен режим <b>Проверка чеков</b>.\n\n"
            "Отправь PDF-файл чека.\n"
            "Либо переключись на <b>Проверка карт</b> и отправь BIN/номер карты.",
            parse_mode="HTML",
            reply_markup=build_menu(is_admin_user(update), mode)
        )
        return

    await update.message.reply_text(
        "❌ В режиме <b>Проверка чеков</b> нужно отправить PDF-файл.\n\n"
        "Для BIN/карты переключись на <b>Проверка карт</b>.",
        parse_mode="HTML",
        reply_markup=build_menu(is_admin_user(update), mode)
    )


# =========================
# HTTP server
# =========================
def build_web_app(application: Application) -> web.Application:
    app = web.Application()

    async def health_check(request):
        return web.Response(text="OK", status=200)

    async def telegram_webhook(request: web.Request):
        if WEBHOOK_SECRET:
            secret_hdr = request.headers.get("X-Telegram-Bot-Api-Secret-Token", "")
            if secret_hdr != WEBHOOK_SECRET:
                return web.Response(text="Forbidden", status=403)

        data = await request.json()
        upd = Update.de_json(data, application.bot)
        await application.update_queue.put(upd)
        return web.Response(text="OK", status=200)

    app.router.add_get("/", health_check)
    app.router.add_get("/health", health_check)
    app.router.add_post("/telegram", telegram_webhook)
    return app


async def run_http_server(port: int, application: Application):
    app = build_web_app(application)
    runner = web.AppRunner(app)
    await runner.setup()
    site = web.TCPSite(runner, "0.0.0.0", port)
    await site.start()
    logger.info(f"HTTP-сервер запущен на порту {port}")
    return runner


# =========================
# Run bot
# =========================
async def run_bot():
    if not load_db():
        logger.critical("Не удалось загрузить базу BIN-кодов!")
        return

    token = os.getenv("TELEGRAM_TOKEN")
    if not token:
        logger.error("TELEGRAM_TOKEN не найден!")
        return

    await db_init()

    application = (
        Application.builder()
        .token(token)
        .concurrent_updates(True)
        .build()
    )

    application.add_handler(CommandHandler("start", start))
    application.add_handler(CommandHandler("stats", stats_cmd))
    application.add_handler(CommandHandler("broadcast", broadcast_cmd))
    application.add_handler(CommandHandler("cancel", cancel_cmd))
    application.add_handler(CommandHandler("grant_unlimited", grant_unlimited_cmd))
    application.add_handler(CommandHandler("user_access", user_access_cmd))

    application.add_handler(CallbackQueryHandler(flag_callback, pattern=r"^(flag:|flag_yes:|flag_no:)"))
    application.add_handler(MessageHandler(filters.Document.ALL, handle_document))
    application.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_text))

    port = int(os.environ.get("PORT", 8080))

    logger.info("Бот запускается...")
    await application.initialize()
    await application.start()

    http_runner = await run_http_server(port, application)

    if not WEBHOOK_URL:
        logger.error("WEBHOOK_URL не задан! Добавь WEBHOOK_URL=https://<service>.onrender.com/telegram")
    else:
        await application.bot.set_webhook(
            url=WEBHOOK_URL,
            secret_token=WEBHOOK_SECRET or None,
            drop_pending_updates=True
        )
        logger.info(f"Webhook установлен: {WEBHOOK_URL}")

    try:
        while True:
            await asyncio.sleep(3600)
    except asyncio.CancelledError:
        logger.info("Получен сигнал остановки")
    except Exception as e:
        logger.error(f"Критическая ошибка: {e}")
    finally:
        logger.info("Остановка бота...")
        try:
            if WEBHOOK_URL:
                await application.bot.delete_webhook(drop_pending_updates=False)
        except Exception:
            pass

        try:
            global _http_session
            if _http_session and not _http_session.closed:
                await _http_session.close()
        except Exception:
            pass

        try:
            global _db_pool
            if _db_pool is not None:
                await _db_pool.close()
        except Exception:
            pass

        await application.stop()
        await application.shutdown()
        await http_runner.cleanup()
        logger.info("Бот успешно остановлен")


if __name__ == "__main__":
    try:
        asyncio.run(run_bot())
    except KeyboardInterrupt:
        logger.info("Бот остановлен по запросу пользователя")
    except Exception as e:
        logger.error(f"Фатальная ошибка: {str(e)}")
