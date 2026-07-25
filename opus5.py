"""Polymarket crypto trading bot (CLOB)."""

from __future__ import annotations
import warnings
warnings.filterwarnings('ignore', category=DeprecationWarning)
import argparse
import asyncio
import base64
import bisect
import concurrent.futures
import csv
import hashlib
import heapq
import hmac
import importlib.metadata
import itertools
import json
import logging
import math
import os
import random
import re
import signal
import sys
import threading
import time
import zlib
if os.name == 'nt':
    import msvcrt as _file_lock_mod
else:
    import fcntl as _file_lock_mod
from collections import Counter, deque
from dataclasses import dataclass, field
from datetime import datetime, timezone
from decimal import Decimal, InvalidOperation, ROUND_CEILING, ROUND_FLOOR
from enum import Enum
from pathlib import Path
from typing import Any, Callable, ClassVar, Deque, Dict, List, Optional, Set, Tuple
from urllib.parse import urlencode

def _check_deps() -> None:
    missing = []
    for mod, pkg in [('aiohttp', 'aiohttp'), ('websockets', 'websockets'), ('eth_account', 'eth-account'), ('web3', 'web3')]:
        try:
            __import__(mod)
        except ImportError:
            missing.append(pkg)
    if missing:
        print(f"Missing packages â€” run:  pip install {' '.join(missing)}")
        sys.exit(1)
_check_deps()
import aiohttp
import websockets
from eth_account import Account
from web3 import Web3
from web3.exceptions import TransactionNotFound
try:
    from dotenv import load_dotenv
    load_dotenv(override=False)
except ImportError:
    pass
_HAS_SDK = False
_SDK_IS_V2 = False
try:
    from py_clob_client_v2.client import ClobClient
    from py_clob_client_v2.clob_types import BalanceAllowanceParams, OrderArgs, OrderType, PartialCreateOrderOptions
    from py_clob_client_v2.order_builder.constants import BUY as _SDK_BUY, SELL as _SDK_SELL
    _HAS_SDK = True
    _SDK_IS_V2 = True
except ImportError:
    try:
        from py_clob_client.client import ClobClient
        from py_clob_client.clob_types import BalanceAllowanceParams, OrderArgs, OrderType, PartialCreateOrderOptions
        from py_clob_client.order_builder.constants import BUY as _SDK_BUY, SELL as _SDK_SELL
        _HAS_SDK = True
    except ImportError:
        pass
try:
    from py_clob_client_v2.clob_types import AssetType
except ImportError:
    try:
        from py_clob_client.clob_types import AssetType
    except ImportError:
        AssetType = None
try:
    import colorlog
    _HAS_COLOR = True
except ImportError:
    _HAS_COLOR = False
try:
    import orjson as _json_mod

    def _json_loads(data):
        return _json_mod.loads(data)

    def _json_dumps(obj):
        return _json_mod.dumps(obj).decode()
    _FAST_JSON = True
except ImportError:
    _json_mod = json
    _json_loads = json.loads
    _json_dumps = json.dumps
    _FAST_JSON = False
_BOT_VERSION = 'v19.5.9e-oracle-latarb-recovery'
VENUE_MIN_ORDER_USDC: float = 2.0
GBM_SIGMA_FLOOR_PER_SEC: float = 0.00025
# Live LatArb + shadow reject when BOTH books are older than this (local age).
# Offline analyze/go-no-go must use the same constant (parity).
LATARB_DUAL_BOOK_STALE_MS: float = 250.0  # D2 FIX: was 2000ms; both books must be fresh for lat-arb
LATARB_STATE_PATH: str = '~/latarb_state.json'
LATARB_FILLS_PATH: str = '~/latarb_fills.jsonl'
LATARB_SETTLE_PATH: str = '~/latarb_settle.jsonl'
# Live kill: pause LatArb when rolling fill rate stays below this after enough FAK attempts.
# E1 FIX: renamed from LATARB_MIN_LIVE_FILL_RATE — that name collided with the
# env var / config field of the live-proof sizing gate (default 0.40), so
# setting the env var silently did NOT move this kill switch.  The kill switch
# now has its own env knob; default behavior unchanged (0.20).
LATARB_KILL_SWITCH_MIN_FILL_RATE: float = float(os.environ.get('LATARB_KILL_SWITCH_MIN_FILL_RATE', '0.20'))
LATARB_MIN_LIVE_ATTEMPTS_FOR_KILL: int = 30
LATARB_KILL_WINDOW: int = 50
LATARB_KILL_COOLDOWN_S: float = 900.0
# Default taker-delay horizon (s) when order-latency metrics are cold.
LATARB_DEFAULT_TAKER_DELAY_S: float = 0.25
# K7 FIX: hold this long before a fatal preflight exit (underfunded / balance
# unverifiable) so a Restart=always supervisor cannot crash-loop every ~5s.
FATAL_PREFLIGHT_HOLD_S: float = 600.0

class FatalBotError(RuntimeError):
    pass

def acquire_instance_lock(cfg: 'Config') -> Any:
    identity = cfg.proxy_address or hashlib.sha256((cfg.private_key or 'dry-run').encode()).hexdigest()[:16]
    safe = re.sub('[^A-Za-z0-9_.-]+', '_', identity)[:80] or 'default'
    lock_dir = os.path.expanduser('~')
    path = os.path.join(lock_dir, f'polybot_{safe}.lock')
    fh = open(path, 'a+', encoding='utf-8')
    try:
        if os.name == 'nt':
            fh.seek(0, os.SEEK_END)
            if fh.tell() == 0:
                fh.write('0')
                fh.flush()
            fh.seek(0)
            _file_lock_mod.locking(fh.fileno(), _file_lock_mod.LK_NBLCK, 1)
        else:
            _file_lock_mod.flock(fh.fileno(), _file_lock_mod.LOCK_EX | _file_lock_mod.LOCK_NB)
    except OSError as exc:
        try:
            fh.close()
        except Exception:
            pass
        raise FatalBotError(f'Another Polymarket bot instance is already running for {identity}; stop it before starting this process') from exc
    fh.seek(0)
    fh.truncate()
    fh.write(f'pid={os.getpid()} started={datetime.now(timezone.utc).isoformat()}\n')
    fh.flush()
    return fh
_SIG_LABELS: Dict[int, str] = {0: 'EOA', 1: 'POLY_PROXY', 2: 'POLY_GNOSIS_SAFE'}
_PROCESS_INSTANCE_LOCK: Optional[Any] = None
_DECIMALS = 6
_SCALE = 10 ** _DECIMALS
_FILL_EPS_INT: int = 0
_CALIB_FLUSH_EVERY: int = 25

def get_logger(name: str, level: str='INFO') -> logging.Logger:
    logger = logging.getLogger(name)
    if logger.handlers:
        return logger
    logger.setLevel(getattr(logging, level.upper(), logging.INFO))
    if _HAS_COLOR:
        h = colorlog.StreamHandler(sys.stdout)
        h.setFormatter(colorlog.ColoredFormatter('%(asctime)s.%(msecs)03d %(log_color)s[%(name)-14s]%(reset)s %(levelname)-8s %(message)s', datefmt='%H:%M:%S', log_colors={'DEBUG': 'cyan', 'INFO': 'green', 'WARNING': 'yellow', 'ERROR': 'red', 'CRITICAL': 'bold_red'}))
    else:
        h = logging.StreamHandler(sys.stdout)
        h.setFormatter(logging.Formatter('%(asctime)s.%(msecs)03d [%(name)-14s] %(levelname)-8s %(message)s', datefmt='%H:%M:%S'))
    logger.addHandler(h)
    logger.propagate = False
    return logger
for _q in ('websockets', 'urllib3', 'web3'):
    logging.getLogger(_q).setLevel(logging.WARNING)
logging.getLogger('aiohttp').setLevel(logging.INFO)
logging.getLogger('py_clob_client_v2').setLevel(logging.CRITICAL)
log = get_logger('Bot')

@dataclass
class Config:
    private_key: str = ''
    proxy_address: str = ''
    signature_type: int = 2
    clob_url: str = 'https://clob.polymarket.com'
    gamma_url: str = 'https://gamma-api.polymarket.com'
    chain_id: int = 137
    coins: List[str] = field(default_factory=lambda: ['BTC', 'ETH', 'SOL'])
    min_order_size: float = 2.0
    max_order_size: float = 25.0
    max_position: float = 100.0
    max_bankroll_fraction: float = 0.1
    max_daily_loss: float = 50.0
    max_daily_loss_pct: float = 0.05
    max_monthly_loss: float = 800.0
    max_drawdown_from_peak: float = 50.0
    max_open_orders: int = 15
    rate_limit: int = 12
    book_max_age_ms: float = 500.0
    max_net_exposure_usdc: float = 200.0
    dry_run: bool = True
    log_level: str = 'INFO'
    min_edge: float = 0.012
    entry_start_s: int = 15
    entry_end_s: int = 260
    strategy_interval_s: float = 1.5
    kelly_fraction: float = 0.18
    sustain_ticks: int = 1
    stop_loss_prob: float = 0.43
    forced_exit_ttc_s: int = 25
    latency_arb_enabled: bool = False
    latency_arb_edge: float = 0.02
    latency_arb_cooldown: float = 2.0
    latency_arb_min_prob: float = 0.58
    require_latarb_proven_edge: bool = True
    latarb_min_proven_signals: int = 200
    latarb_min_win_rate: float = 0.52
    latarb_min_total_pnl: float = 0.0
    # Live proof (fills + settlement ledger) â€” stricter than shadow-only GO.
    require_latarb_live_proof: bool = False
    latarb_bootstrap_live: bool = True
    latarb_min_live_attempts: int = 50
    latarb_min_live_fill_rate: float = 0.4
    latarb_min_settle_samples: int = 20
    latarb_min_settle_win_rate: float = 0.52
    latarb_min_settle_pnl: float = 0.0
    latarb_fills_path: str = '~/latarb_fills.jsonl'
    latarb_settle_path: str = '~/latarb_settle.jsonl'
    complement_arb_enabled: bool = False
    redeem_enabled: bool = False
    polygon_rpc_url: str = 'https://polygon-rpc.com'
    redeem_max_gas_gwei: float = 300.0
    latarb_shadow: bool = True
    latarb_shadow_path: str = '~/latarb_shadow.csv'
    # Transport-age floor; 0 measures liquid books without imposing artificial staleness.
    # LATARB_SHADOW_MAX_AGE_MS remains the stale-quote safety ceiling.
    latarb_shadow_min_age_ms: float = 0.0
    latarb_shadow_throttle_ms: float = 3000.0
    latarb_shadow_max_age_ms: float = 250.0  # D2 FIX: was 2000ms; latency arb requires fresh books
    min_top_book_usdc: float = 6.0
    max_spread_pct: float = 0.1
    max_consecutive_losses: int = 4
    prob_shrink: float = 1.0
    time_decay_exit_ttc_s: int = 90
    ws_shard_count: int = 2
    discovery_interval_s: float = 10.0
    event_driven: bool = True
    eval_debounce_ms: float = 400.0
    max_concurrent_evals: int = 5
    adaptive_kelly: bool = True
    metrics_enabled: bool = True
    dry_run_fill_prob: float = 0.7
    dry_run_latency_ms: float = 50.0
    calibration_log_path: str = '~/calibration.csv'
    calibration_log_enabled: bool = True
    prob_model: str = 'gbm_v183'
    reconcile_fills_interval_s: float = 30.0
    drift_halt_threshold_shares: float = 0.01
    drift_check_concurrency: int = 4
    min_proven_samples: int = 200
    min_proven_edge: float = 0.005
    # Calibrated from calibration_v19 adverse_bps: toxic-only p50â‰ˆ250bps, p75â‰ˆ89
    # on full sample. Cap at 40 so EWMA trips before median toxic regime; 25 was
    # OK but noisy on thin books. Go/no-go uses the same field on mean adverse.
    max_adverse_bps: float = 40.0
    shadow_probe_enabled: bool = True
    adverse_select_gate: bool = True
    adverse_ewma_alpha: float = 0.1
    entry_mode: str = 'maker'
    maker_join_ticks: int = 0
    fast_exit_drop_pct: float = 0.06
    fast_exit_sustain: int = 2
    trail_stop_pct: float = 0.12
    trail_sustain: int = 2
    trail_arm_level: float = 0.65
    forced_exit_hold_if_winning: bool = True
    forced_exit_hold_prob: float = 0.6
    kelly_hold_to_expiry_rate: float = 0.0
    max_gross_exposure_usdc: float = 400.0
    ev_exit_buffer: float = 0.0
    partial_tp_enabled: bool = True
    tp_mode: str = 'confidence'
    tp1_pct: float = 0.35
    tp1_clip_pct: float = 0.4
    tp1_breakeven_stop: bool = True
    conf_scale: float = 1.0
    conf_min_clip: float = 0.3
    conf_max_clip: float = 0.95
    taker_fee_bps: float = 20.0
    category_fee_rate: float = 0.07
    cycle_s: int = 300
    balance_refresh_s: float = 5.0
    maker_gtd_ttl_s: float = 120.0
    capital_shock_pct: float = 0.1
    capital_shock_floor_usdc: float = 2.0
    max_net_bankroll_mult: float = 1.0
    max_gross_bankroll_mult: float = 2.0
    halt_on_capital_shock: bool = True
    per_coin_crossover: bool = True
    auto_flatten_on_halt: bool = False
    spread_edge_mult: float = 0.2
    sigma_edge_mult: float = 0.1
    min_edge_margin: float = 0.005
    momentum_weight: float = 0.0
    market_anchor_weight: float = 0.5
    max_model_disagreement: float = 0.06
    anchor_edge_path: bool = True
    salvage_floor: float = 0.05
    whale_trade_usdc: float = 5000.0
    whale_cooldown_s: float = 3.0

    @property
    def use_proxy(self) -> bool:
        return bool(self.proxy_address)

    @classmethod
    def from_env(cls) -> 'Config':

        def g(k: str, d: str='') -> str:
            raw = os.environ.get(k)
            if raw is None or str(raw).strip() == '':
                return str(d)
            val = str(raw).strip()
            if val[:1] not in ("'", '"'):
                val = re.sub('\\s+#.*$', '', val).strip()
            if len(val) >= 2 and val[0] == val[-1] and (val[0] in ("'", '"')):
                val = val[1:-1].strip()
            return val

        def gi(k: str, d: int) -> int:
            val = g(k, str(d))
            try:
                return int(val)
            except Exception as exc:
                raise ValueError(f'Invalid integer env {k}={val!r}') from exc

        def gf(k: str, d: float) -> float:
            val = g(k, str(d))
            try:
                return float(val)
            except Exception as exc:
                raise ValueError(f'Invalid float env {k}={val!r}') from exc

        def gb(k: str, d: bool) -> bool:
            val = g(k, 'true' if d else 'false').lower()
            if val in ('1', 'true', 'yes', 'y', 'on'):
                return True
            if val in ('0', 'false', 'no', 'n', 'off'):
                return False
            raise ValueError(f'Invalid boolean env {k}={val!r}')
        pk = g('POLYMARKET_PRIVATE_KEY')
        if pk and (not pk.startswith('0x')):
            pk = '0x' + pk
        raw_proxy = g('POLYMARKET_PROXY_ADDRESS') or g('POLYMARKET_FUNDER') or g('POLYMARKET_FUNDER_ADDRESS') or ''
        if raw_proxy and (not raw_proxy.startswith('0x')):
            raw_proxy = '0x' + raw_proxy
        proxy = Web3.to_checksum_address(raw_proxy.lower()) if raw_proxy else ''
        return cls(private_key=pk, proxy_address=proxy, signature_type=gi('POLYMARKET_SIGNATURE_TYPE', 2), clob_url=g('CLOB_URL', g('CLOB_API_URL', 'https://clob.polymarket.com')).rstrip('/ '), gamma_url=g('GAMMA_URL', g('GAMMA_API_URL', 'https://gamma-api.polymarket.com')).rstrip('/ '), chain_id=gi('CHAIN_ID', 137), coins=[c.strip().upper() for c in g('COINS', g('BINANCE_COINS', 'BTC,ETH,SOL')).split(',') if c.strip()], min_order_size=gf('MIN_ORDER_USDC', 2.0), max_order_size=gf('MAX_ORDER_USDC', 25.0), max_position=gf('MAX_POSITION_USDC', 100.0), max_bankroll_fraction=gf('MAX_BANKROLL_FRACTION', 0.1), max_daily_loss=gf('MAX_DAILY_LOSS', 50.0), max_open_orders=gi('MAX_OPEN_ORDERS', 15), rate_limit=gi('ORDER_RATE_LIMIT_PER_SEC', gi('ORDER_RATE_LIMIT', 12)), book_max_age_ms=gf('MAX_BOOK_AGE_MS', 500.0), max_net_exposure_usdc=gf('MAX_NET_EXPOSURE_USDC', 200.0), dry_run=gb('DRY_RUN', True), log_level=g('LOG_LEVEL', 'INFO'), min_edge=gf('MIN_EDGE', 0.012), entry_start_s=gi('ENTRY_START_S', 15), entry_end_s=gi('ENTRY_END_S', 260), strategy_interval_s=gf('STRATEGY_INTERVAL_S', 1.5), kelly_fraction=gf('KELLY_FRACTION', 0.18), sustain_ticks=gi('SUSTAIN_TICKS', 1), stop_loss_prob=gf('STOP_LOSS_PROB', 0.43), forced_exit_ttc_s=gi('FORCED_EXIT_TTC_S', 25), latency_arb_enabled=gb('LATENCY_ARB_ENABLED', False), latency_arb_edge=gf('LATENCY_ARB_EDGE', 0.02), latency_arb_cooldown=gf('LATENCY_ARB_COOLDOWN_S', 2.0), latency_arb_min_prob=gf('LATENCY_ARB_MIN_PROB', 0.58), require_latarb_proven_edge=gb('REQUIRE_LATARB_PROVEN_EDGE', True), latarb_min_proven_signals=gi('LATARB_MIN_PROVEN_SIGNALS', 200), latarb_min_win_rate=gf('LATARB_MIN_WIN_RATE', 0.52), latarb_min_total_pnl=gf('LATARB_MIN_TOTAL_PNL', 0.0), require_latarb_live_proof=gb('REQUIRE_LATARB_LIVE_PROOF', False), latarb_bootstrap_live=gb('LATARB_BOOTSTRAP_LIVE', True), latarb_min_live_attempts=gi('LATARB_MIN_LIVE_ATTEMPTS', 50), latarb_min_live_fill_rate=gf('LATARB_MIN_LIVE_FILL_RATE', 0.4), latarb_min_settle_samples=gi('LATARB_MIN_SETTLE_SAMPLES', 20), latarb_min_settle_win_rate=gf('LATARB_MIN_SETTLE_WIN_RATE', 0.52), latarb_min_settle_pnl=gf('LATARB_MIN_SETTLE_PNL', 0.0), latarb_fills_path=g('LATARB_FILLS_PATH', LATARB_FILLS_PATH), latarb_settle_path=g('LATARB_SETTLE_PATH', '~/latarb_settle.jsonl'), complement_arb_enabled=gb('COMPLEMENT_ARB_ENABLED', False), redeem_enabled=gb('REDEEM_ENABLED', False), polygon_rpc_url=g('POLYGON_RPC_URL', 'https://polygon-rpc.com'), redeem_max_gas_gwei=gf('REDEEM_MAX_GAS_GWEI', 300.0), latarb_shadow=gb('LATARB_SHADOW', True), latarb_shadow_path=g('LATARB_SHADOW_PATH', '~/latarb_shadow.csv'), latarb_shadow_min_age_ms=gf('LATARB_SHADOW_MIN_AGE_MS', 0.0), latarb_shadow_throttle_ms=gf('LATARB_SHADOW_THROTTLE_MS', 3000.0), latarb_shadow_max_age_ms=gf('LATARB_SHADOW_MAX_AGE_MS', 250.0), min_top_book_usdc=gf('MIN_TOP_BOOK_USDC', 6.0), max_spread_pct=gf('MAX_SPREAD_PCT', 0.1), max_consecutive_losses=gi('MAX_CONSECUTIVE_LOSSES', 4), prob_shrink=gf('PROB_SHRINK', 1.0), time_decay_exit_ttc_s=gi('TIME_DECAY_EXIT_TTC_S', 90), ws_shard_count=gi('WS_SHARD_COUNT', 2), discovery_interval_s=gf('DISCOVERY_INTERVAL_S', 10.0), event_driven=gb('EVENT_DRIVEN', True), eval_debounce_ms=gf('EVAL_DEBOUNCE_MS', 400.0), max_concurrent_evals=gi('MAX_CONCURRENT_EVALS', 5), adaptive_kelly=gb('ADAPTIVE_KELLY', True), metrics_enabled=gb('METRICS_ENABLED', True), dry_run_fill_prob=gf('DRY_RUN_FILL_PROB', 0.7), dry_run_latency_ms=gf('DRY_RUN_LATENCY_MS', 50.0), calibration_log_path=g('CALIBRATION_LOG_PATH', '~/calibration.csv'), calibration_log_enabled=gb('CALIBRATION_LOG_ENABLED', True), prob_model=g('PROB_MODEL', 'gbm_v183'), reconcile_fills_interval_s=gf('RECONCILE_FILLS_INTERVAL_S', 30.0), drift_halt_threshold_shares=gf('DRIFT_HALT_THRESHOLD_SHARES', 0.01), drift_check_concurrency=int(gf('DRIFT_CHECK_CONCURRENCY', 4)), min_proven_samples=gi('MIN_PROVEN_SAMPLES', 200), min_proven_edge=gf('MIN_PROVEN_EDGE', 0.005), max_adverse_bps=gf('MAX_ADVERSE_BPS', 40.0), shadow_probe_enabled=gb('SHADOW_PROBE_ENABLED', True), adverse_select_gate=gb('ADVERSE_SELECT_GATE', True), adverse_ewma_alpha=gf('ADVERSE_EWMA_ALPHA', 0.1), entry_mode=g('ENTRY_MODE', 'maker').lower(), maker_join_ticks=gi('MAKER_JOIN_TICKS', 0), fast_exit_drop_pct=gf('FAST_EXIT_DROP_PCT', 0.06), fast_exit_sustain=gi('FAST_EXIT_SUSTAIN', 2), trail_stop_pct=gf('TRAIL_STOP_PCT', 0.12), trail_sustain=gi('TRAIL_SUSTAIN', 2), trail_arm_level=gf('TRAIL_ARM_LEVEL', 0.65), forced_exit_hold_if_winning=gb('FORCED_EXIT_HOLD_IF_WINNING', True), forced_exit_hold_prob=gf('FORCED_EXIT_HOLD_PROB', 0.6), partial_tp_enabled=gb('PARTIAL_TP_ENABLED', True), tp_mode=g('TP_MODE', 'confidence').lower(), tp1_pct=gf('TP1_PCT', 0.35), tp1_clip_pct=gf('TP1_CLIP_PCT', 0.4), tp1_breakeven_stop=gb('TP1_BREAKEVEN_STOP', True), conf_scale=gf('CONF_SCALE', 1.0), conf_min_clip=gf('CONF_MIN_CLIP', 0.3), conf_max_clip=gf('CONF_MAX_CLIP', 0.95), taker_fee_bps=gf('TAKER_FEE_BPS', 20.0), category_fee_rate=gf('CATEGORY_FEE_RATE', 0.07), cycle_s=gi('CYCLE_S', 300), balance_refresh_s=gf('BALANCE_REFRESH_S', 5.0), maker_gtd_ttl_s=gf('MAKER_GTD_TTL_S', 120.0), capital_shock_pct=gf('CAPITAL_SHOCK_PCT', 0.1), capital_shock_floor_usdc=gf('CAPITAL_SHOCK_FLOOR_USDC', 2.0), max_net_bankroll_mult=gf('MAX_NET_BANKROLL_MULT', 1.0), max_gross_bankroll_mult=gf('MAX_GROSS_BANKROLL_MULT', 2.0), halt_on_capital_shock=gb('HALT_ON_CAPITAL_SHOCK', True), per_coin_crossover=gb('PER_COIN_CROSSOVER', True), auto_flatten_on_halt=gb('AUTO_FLATTEN_ON_HALT', False), spread_edge_mult=gf('SPREAD_EDGE_MULT', 0.2), sigma_edge_mult=gf('SIGMA_EDGE_MULT', 0.1), kelly_hold_to_expiry_rate=gf('KELLY_HOLD_TO_EXPIRY_RATE', 0.0), max_gross_exposure_usdc=gf('MAX_GROSS_EXPOSURE_USDC', 400.0), ev_exit_buffer=gf('EV_EXIT_BUFFER', 0.0), max_daily_loss_pct=gf('MAX_DAILY_LOSS_PCT', 0.05), max_monthly_loss=gf('MAX_MONTHLY_LOSS', 800.0), max_drawdown_from_peak=gf('MAX_DRAWDOWN_FROM_PEAK', 50.0), min_edge_margin=gf('MIN_EDGE_MARGIN', 0.005), momentum_weight=gf('MOMENTUM_WEIGHT', 0.0), market_anchor_weight=gf('MARKET_ANCHOR_WEIGHT', 0.5), max_model_disagreement=gf('MAX_MODEL_DISAGREEMENT', 0.06), anchor_edge_path=gb('ANCHOR_EDGE_PATH', True), salvage_floor=gf('SALVAGE_FLOOR', 0.05), whale_trade_usdc=gf('WHALE_TRADE_USDC', 5000.0), whale_cooldown_s=gf('WHALE_COOLDOWN_S', 3.0)).rescale_for_cycle()

    def rescale_for_cycle(self) -> 'Config':
        if self.cycle_s != 300 and self.cycle_s > 0:
            scale = self.cycle_s / 300.0
            if self.entry_start_s == 15:
                self.entry_start_s = int(round(15 * scale))
            if self.entry_end_s == 260:
                self.entry_end_s = int(round(260 * scale))
            if self.forced_exit_ttc_s == 25:
                self.forced_exit_ttc_s = int(round(25 * scale))
            if self.time_decay_exit_ttc_s == 90:
                self.time_decay_exit_ttc_s = int(round(90 * scale))
        return self

    def validate(self) -> List[str]:
        errs: List[str] = []
        for _name, _field in self.__dataclass_fields__.items():
            if _field.type in (float, 'float'):
                _val = getattr(self, _name)
                if not math.isfinite(_val):
                    errs.append(f'{_name} must be finite, got {_val}')
        if not self.dry_run and (not self.private_key):
            errs.append('POLYMARKET_PRIVATE_KEY is required for live trading')
        if not self.dry_run and self.latency_arb_enabled and (not self.redeem_enabled):
            errs.append('REDEEM_ENABLED=true is required for live LatArb so resolved CTF collateral cannot be stranded')
        if not self.dry_run and self.redeem_enabled and self.signature_type == 1:
            errs.append('Live redemption does not support POLYMARKET_SIGNATURE_TYPE=1 proxy wallets; use verified signature type 2 Safe routing or disable live trading')
        if self.min_order_size <= 0 or self.max_order_size < self.min_order_size:
            errs.append('Order size config is invalid')
        if self.min_order_size < VENUE_MIN_ORDER_USDC:
            errs.append(f'min_order_size (${self.min_order_size:.2f}) is below the Polymarket venue minimum (${VENUE_MIN_ORDER_USDC:.2f})')
        if self.max_order_size < VENUE_MIN_ORDER_USDC:
            errs.append(f'max_order_size (${self.max_order_size:.2f}) is below the Polymarket venue minimum (${VENUE_MIN_ORDER_USDC:.2f})')
        if not self.dry_run and (not self.require_latarb_proven_edge):
            errs.append('REQUIRE_LATARB_PROVEN_EDGE=false is not allowed while DRY_RUN=false; live LatArb requires proven edge')
        if self.latency_arb_enabled and self.require_latarb_proven_edge:
            if self.latarb_min_proven_signals <= 0:
                errs.append('LATARB_MIN_PROVEN_SIGNALS must be > 0')
            if not 0.0 <= self.latarb_min_win_rate <= 1.0:
                errs.append('LATARB_MIN_WIN_RATE must be in [0, 1]')
        # model_prob is hard-clamped to [0.3, 0.85] in LatArb â€” reject impossible config
        if self.latency_arb_min_prob > 0.85:
            errs.append(f'LATENCY_ARB_MIN_PROB={self.latency_arb_min_prob} > 0.85 model_prob cap makes LatArb impossible')
        if self.rate_limit <= 0:
            errs.append(f'rate_limit must be positive, got {self.rate_limit}')
        if self.max_order_size < 2 * self.min_order_size:
            log.warning('max_order_size ($%.1f) < 2x min_order_size ($%.1f) â€” Kelly sizing is effectively disabled; all trades will fire at the venue minimum', self.max_order_size, self.min_order_size)
        if self.max_position < self.max_order_size:
            errs.append(f'max_position ({self.max_position}) < max_order_size ({self.max_order_size})')
        if not 0.0 < self.max_bankroll_fraction <= 1.0:
            errs.append(f'max_bankroll_fraction must be in (0, 1], got {self.max_bankroll_fraction}')
        if not 0.0 < self.kelly_fraction <= 1.0:
            errs.append(f'kelly_fraction must be in (0, 1], got {self.kelly_fraction}')
        if not 0.0 < self.stop_loss_prob < 1.0:
            errs.append(f'stop_loss_prob must be in (0, 1), got {self.stop_loss_prob}')
        if not 0.0 <= self.min_edge < 1.0:
            errs.append(f'min_edge must be in [0, 1), got {self.min_edge}')
        if self.max_daily_loss <= 0.0:
            errs.append(f'max_daily_loss must be > 0, got {self.max_daily_loss}')
        if not 0.0 <= self.max_daily_loss_pct <= 1.0:
            errs.append(f'max_daily_loss_pct must be in [0, 1], got {self.max_daily_loss_pct}')
        if self.entry_mode not in ('taker', 'maker'):
            errs.append(f"entry_mode must be 'taker' or 'maker', got {self.entry_mode}")
        if not 0.0 < self.adverse_ewma_alpha <= 1.0:
            errs.append(f'adverse_ewma_alpha must be in (0, 1], got {self.adverse_ewma_alpha}')
        if not 0.0 < self.tp1_pct < 5.0:
            errs.append(f'tp1_pct must be in (0, 5), got {self.tp1_pct}')
        if not 0.1 <= self.tp1_clip_pct <= 0.95:
            errs.append(f'tp1_clip_pct must be in [0.10, 0.95], got {self.tp1_clip_pct}')
        if self.tp_mode not in ('fixed', 'confidence'):
            errs.append(f"tp_mode must be 'fixed' or 'confidence', got {self.tp_mode}")
        if not 0.1 <= self.conf_min_clip <= self.conf_max_clip <= 1.0:
            errs.append(f'conf_min_clip/conf_max_clip invalid: [{self.conf_min_clip}, {self.conf_max_clip}]')
        if not 0.0 <= self.kelly_hold_to_expiry_rate <= 1.0:
            errs.append(f'kelly_hold_to_expiry_rate must be in [0, 1], got {self.kelly_hold_to_expiry_rate}')
        if self.max_gross_exposure_usdc <= 0.0:
            errs.append(f'max_gross_exposure_usdc must be > 0, got {self.max_gross_exposure_usdc}')
        if self.maker_gtd_ttl_s < 0.0:
            errs.append(f'maker_gtd_ttl_s must be >= 0, got {self.maker_gtd_ttl_s}')
        elif 0.0 < self.maker_gtd_ttl_s < 120.0:
            errs.append(f'maker_gtd_ttl_s must be 0 (dry-run GTC only) or >= 120: Polymarket requires expiration >= now+180s and expires GTD 60s early (got {self.maker_gtd_ttl_s})')
        if not self.dry_run and self.entry_mode == 'maker':
            if self.maker_gtd_ttl_s < 120.0:
                errs.append('LIVE ENTRY_MODE=maker requires MAKER_GTD_TTL_S >= 120 (venue-backed GTD; 0/GTC is not permitted for live makers)')
            if _HAS_SDK and OrderType is not None and (not hasattr(OrderType, 'GTD')):
                errs.append('LIVE ENTRY_MODE=maker requires SDK OrderType.GTD (install py-clob-client-v2; refuse silent GTC downgrade)')
            if _HAS_SDK and OrderArgs is not None:
                try:
                    import inspect as _insp
                    _sig = _insp.signature(OrderArgs)
                    if 'expiration' not in _sig.parameters:
                        errs.append('LIVE ENTRY_MODE=maker requires OrderArgs(expiration=...) support in the installed CLOB SDK')
                except (TypeError, ValueError):
                    pass
        if not 0.0 < self.capital_shock_pct <= 1.0:
            errs.append(f'capital_shock_pct must be in (0, 1], got {self.capital_shock_pct}')
        if self.capital_shock_floor_usdc < 0.0:
            errs.append(f'capital_shock_floor_usdc must be >= 0, got {self.capital_shock_floor_usdc}')
        if self.max_net_bankroll_mult <= 0.0:
            errs.append(f'max_net_bankroll_mult must be > 0, got {self.max_net_bankroll_mult}')
        if self.max_gross_bankroll_mult <= 0.0:
            errs.append(f'max_gross_bankroll_mult must be > 0, got {self.max_gross_bankroll_mult}')
        if self.ev_exit_buffer < 0.0:
            errs.append(f'ev_exit_buffer must be >= 0, got {self.ev_exit_buffer}')
        if not 0.0 <= self.latency_arb_min_prob <= 1.0:
            errs.append(f'latency_arb_min_prob must be in [0, 1], got {self.latency_arb_min_prob}')
        if self.max_drawdown_from_peak < 0.0:
            errs.append(f'max_drawdown_from_peak must be >= 0, got {self.max_drawdown_from_peak}')
        if self.complement_arb_enabled:
            errs.append('COMPLEMENT_ARB_ENABLED=true is unsafe in this build; keep it false until the two-leg arb is depth-walked and atomic')
        return errs

def _tick_decimals(tick_size: float) -> int:
    if not isinstance(tick_size, (int, float)) or not math.isfinite(tick_size) or tick_size <= 0.0:
        return 2
    try:
        return max(0, -Decimal(str(tick_size)).normalize().as_tuple().exponent)
    except (InvalidOperation, TypeError, ValueError):
        return 2

def snap_price(price: float, tick_size: float, side: str='BUY', _decimals: Optional[int]=None, _max_ticks: Optional[int]=None) -> float:
    if not isinstance(price, (int, float)) or not math.isfinite(price) or price <= 0.0:
        raise ValueError(f'snap_price: invalid price {price!r}')
    if not isinstance(tick_size, (int, float)) or not math.isfinite(tick_size) or tick_size <= 0.0:
        tick_size = 0.01
    if _decimals is None:
        _decimals = _tick_decimals(tick_size)
    if _max_ticks is None:
        _max_ticks = int(round(1.0 / tick_size)) - 1
    scale = 10 ** _decimals
    tick_int = int(Decimal(str(tick_size)) * scale)
    if tick_int <= 0:
        return round(price, _decimals)
    q = Decimal(str(price)) / Decimal(str(tick_size))
    if side == 'SELL':
        price_ticks = int(q.to_integral_value(rounding=ROUND_CEILING))
    else:
        price_ticks = int(q.to_integral_value(rounding=ROUND_FLOOR))
    price_ticks = max(1, min(_max_ticks, int(price_ticks)))
    return round(price_ticks * tick_int / scale, _decimals)
_USDC_DECIMALS: int = 6
_USDC_SCALE: int = 10 ** _USDC_DECIMALS

def _parse_bal_micro(raw: Any) -> int:
    s = str(raw).strip().replace(',', '')
    if not s or s in ('0', 'None', 'null'):
        return 0
    sign = 1
    if s[0] == '-':
        sign = -1
        s = s[1:]
    elif s[0] == '+':
        s = s[1:]
    if not s:
        return 0
    try:
        if 'e' in s or 'E' in s:
            micro = int(Decimal(s) * _USDC_SCALE)
            return sign * micro
        if '.' in s:
            whole, frac = s.split('.', 1)
            if '.' in frac:
                return 0
            whole = whole or '0'
            frac = frac[:_USDC_DECIMALS].ljust(_USDC_DECIMALS, '0')
            if not (whole.isdigit() and frac.isdigit()):
                return 0
            micro = int(whole) * _USDC_SCALE + int(frac)
        else:
            if not s.isdigit():
                return 0
            micro = int(s)
    except (ValueError, TypeError, InvalidOperation):
        return 0
    return sign * micro

def _parse_bal(raw: Any) -> float:
    micro = _parse_bal_micro(raw)
    if micro < 0:
        return 0.0
    v = micro / _USDC_SCALE
    if not math.isfinite(v):
        return 0.0
    if v > 1000000:
        logging.getLogger('Bot').warning("Suspicious balance parse: raw=%r -> %.2f USDC. Verify CLOB API response format hasn't changed.", raw, v)
    return v

def _try_parse_balance_field(raw: Any) -> Optional[float]:
    if raw is None:
        return None
    s = str(raw).strip().replace(',', '')
    if not s:
        return None
    low = s.lower()
    if low in ('none', 'null', 'nan', 'undefined', 'true', 'false'):
        return None
    sign = 1
    if s[0] == '-':
        return None
    if s[0] == '+':
        s = s[1:]
    if not s:
        return None
    try:
        if 'e' in s or 'E' in s:
            micro = int(Decimal(s) * _USDC_SCALE)
        elif '.' in s:
            whole, frac = s.split('.', 1)
            if '.' in frac:
                return None
            whole = whole or '0'
            frac = frac[:_USDC_DECIMALS].ljust(_USDC_DECIMALS, '0')
            if not (whole.isdigit() and frac.isdigit()):
                return None
            micro = int(whole) * _USDC_SCALE + int(frac)
        else:
            if not s.isdigit():
                return None
            micro = int(s)
    except (ValueError, TypeError, InvalidOperation, ArithmeticError):
        return None
    if micro < 0:
        return None
    v = micro / _USDC_SCALE
    if not math.isfinite(v):
        return None
    if v > 1000000:
        logging.getLogger('Bot').warning("Suspicious balance parse: raw=%r -> %.2f USDC. Verify CLOB API response format hasn't changed.", raw, v)
    return float(v)

def _try_parse_balance_payload(resp: Any) -> Optional[float]:
    if not isinstance(resp, dict):
        return None
    if 'balance' not in resp:
        return None
    return _try_parse_balance_field(resp.get('balance'))

def _pkg_version(name: str) -> str:
    try:
        return importlib.metadata.version(name)
    except Exception:
        return 'unknown'

def _lookup_proxy_address(eoa: str, chain_id: int=137) -> Optional[str]:
    eoa_cs = Web3.to_checksum_address(eoa)
    FACTORIES = [('0xaB45c5A4B0c941a2F231C04C3f49182e1A254052', 'getProxy'), ('0x4bFb41d5B3570DeFd03C39a9A4D8dE6Bd8B8982E', 'getProxyAddress'), ('0x4bFb41d5B3570DeFd03C39a9A4D8dE6Bd8B8982E', 'getSafeAddress')]
    RPC_URLS = ['https://polygon-rpc.com', 'https://rpc.ankr.com/polygon', 'https://polygon.llamarpc.com', 'https://polygon.drpc.org']
    for factory_addr, fn_name in FACTORIES:
        ABI = [{'inputs': [{'name': '_owner', 'type': 'address'}], 'name': fn_name, 'outputs': [{'name': '', 'type': 'address'}], 'stateMutability': 'view', 'type': 'function'}]
        for rpc in RPC_URLS:
            try:
                w3 = Web3(Web3.HTTPProvider(rpc, request_kwargs={'timeout': 5}))
                ct = w3.eth.contract(address=Web3.to_checksum_address(factory_addr), abi=ABI)
                fn = getattr(ct.functions, fn_name)
                result = fn(eoa_cs).call()
                if result and result != '0x' + '0' * 40:
                    return Web3.to_checksum_address(result)
            except Exception:
                continue
    return None

class Side(str, Enum):
    BUY = 'BUY'
    SELL = 'SELL'

class Strategy(str, Enum):
    MM = 'mm'
    S2O = 's2o'
    TEMPORAL = 'temporal'

@dataclass
class OrderBook:
    PRICE_SCALE: ClassVar[int] = 10000
    SIZE_SCALE: ClassVar[int] = 1000000
    token_id: str
    _bids_int: Dict[int, int] = field(default_factory=dict)
    _asks_int: Dict[int, int] = field(default_factory=dict)
    # Local receipt time (monotonic) â€” transport age for LatArb stale-quote gate.
    ts: float = field(default_factory=time.monotonic)
    # Venue message timestamp (ms epoch) when present; used to reject out-of-order depth.
    exchange_ts_ms: Optional[int] = None
    _bid_size_total: int = 0
    _ask_size_total: int = 0
    _best_bid_key: Optional[int] = None
    _best_ask_key: Optional[int] = None
    _cached_bids: List[Tuple[float, float]] = field(default_factory=list)
    _cached_asks: List[Tuple[float, float]] = field(default_factory=list)
    _sorted_dirty: bool = True
    _snapshot_ts: float = 0.0

    def touch(self, recv_mono: Optional[float]=None, exchange_ts_ms: Optional[int]=None, *, allow_regression: bool=False) -> bool:
        """Update clocks. Returns False if exchange_ts is a regression (skip applying that delta)."""
        now = float(recv_mono) if recv_mono is not None else time.monotonic()
        if exchange_ts_ms is not None:
            try:
                ets = int(exchange_ts_ms)
            except (TypeError, ValueError):
                ets = 0
            if ets > 0:
                prev = self.exchange_ts_ms
                # 100ms tolerance: venues sometimes emit near-equal stamps out of order.
                if (not allow_regression) and prev is not None and ets + 100 < prev:
                    return False
                self.exchange_ts_ms = ets if prev is None else max(prev, ets)
        self.ts = now
        return True

    @classmethod
    def _price_to_key(cls, price: float) -> int:
        return int(round(price * cls.PRICE_SCALE))

    @classmethod
    def _key_to_price(cls, key: int) -> float:
        return key / cls.PRICE_SCALE

    @classmethod
    def _size_to_int(cls, size: float) -> int:
        return int(round(size * cls.SIZE_SCALE))

    @classmethod
    def _int_to_size(cls, size_int: int) -> float:
        return size_int / cls.SIZE_SCALE

    def apply_delta(self, price: float, size: float, is_bid: bool) -> None:
        if not math.isfinite(price) or not math.isfinite(size) or price <= 0 or (size < 0):
            return
        key = self._price_to_key(price)
        new_size_int = self._size_to_int(size) if size > 0 else 0
        target = self._bids_int if is_bid else self._asks_int
        old_size_int = target.get(key, 0)
        if new_size_int <= 0:
            if key in target:
                del target[key]
            new_size_int = 0
        else:
            target[key] = new_size_int
        delta = new_size_int - old_size_int
        if is_bid:
            self._bid_size_total += delta
            if new_size_int == 0:
                if self._best_bid_key == key:
                    self._best_bid_key = None
            elif self._best_bid_key is None or key > self._best_bid_key:
                self._best_bid_key = key
        else:
            self._ask_size_total += delta
            if new_size_int == 0:
                if self._best_ask_key == key:
                    self._best_ask_key = None
            elif self._best_ask_key is None or key < self._best_ask_key:
                self._best_ask_key = key
        self._sorted_dirty = True

    def replace_snapshot(self, bids: List[Tuple[float, float]], asks: List[Tuple[float, float]]) -> None:
        seen_bid_keys: Set[int] = set()
        self._bids_int = {}
        for p, s in bids:
            if math.isfinite(p) and math.isfinite(s) and (p > 0) and (s > 0):
                k = self._price_to_key(p)
                if k in seen_bid_keys:
                    continue
                seen_bid_keys.add(k)
                self._bids_int[k] = self._bids_int.get(k, 0) + self._size_to_int(s)
        seen_ask_keys: Set[int] = set()
        self._asks_int = {}
        for p, s in asks:
            if math.isfinite(p) and math.isfinite(s) and (p > 0) and (s > 0):
                k = self._price_to_key(p)
                if k in seen_ask_keys:
                    continue
                seen_ask_keys.add(k)
                self._asks_int[k] = self._asks_int.get(k, 0) + self._size_to_int(s)
        self._bid_size_total = sum(self._bids_int.values())
        self._ask_size_total = sum(self._asks_int.values())
        self._best_bid_key = max(self._bids_int) if self._bids_int else None
        self._best_ask_key = min(self._asks_int) if self._asks_int else None
        self._sorted_dirty = True
        self._snapshot_ts = time.monotonic()

    def refresh_totals(self) -> None:
        self._bid_size_total = sum(self._bids_int.values())
        self._ask_size_total = sum(self._asks_int.values())

    def _resolve_best_bid_key(self) -> Optional[int]:
        bbk = self._best_bid_key
        if bbk is not None and self._bids_int.get(bbk, 0) > 0:
            return bbk
        if self._bids_int:
            self._best_bid_key = max(self._bids_int)
            return self._best_bid_key
        self._best_bid_key = None
        return None

    def _resolve_best_ask_key(self) -> Optional[int]:
        bak = self._best_ask_key
        if bak is not None and self._asks_int.get(bak, 0) > 0:
            return bak
        if self._asks_int:
            self._best_ask_key = min(self._asks_int)
            return self._best_ask_key
        self._best_ask_key = None
        return None

    def _ensure_sorted(self) -> None:
        if not self._sorted_dirty:
            return
        inv_p = 1.0 / self.PRICE_SCALE
        inv_s = 1.0 / self.SIZE_SCALE
        self._cached_bids = [(k * inv_p, v * inv_s) for k, v in sorted(self._bids_int.items(), reverse=True)]
        self._cached_asks = [(k * inv_p, v * inv_s) for k, v in sorted(self._asks_int.items())]
        self._sorted_dirty = False

    @property
    def bids(self) -> List[Tuple[float, float]]:
        self._ensure_sorted()
        return self._cached_bids

    @property
    def asks(self) -> List[Tuple[float, float]]:
        self._ensure_sorted()
        return self._cached_asks

    @property
    def best_bid(self) -> Optional[float]:
        k = self._resolve_best_bid_key()
        return None if k is None else k / self.PRICE_SCALE

    @property
    def best_ask(self) -> Optional[float]:
        k = self._resolve_best_ask_key()
        return None if k is None else k / self.PRICE_SCALE

    @property
    def mid(self) -> Optional[float]:
        bb, ba = (self.best_bid, self.best_ask)
        if bb is not None and ba is not None:
            return (bb + ba) / 2
        return bb if bb is not None else ba

    @property
    def micro_price(self) -> Optional[float]:
        if not self._bids_int or not self._asks_int:
            return self.mid
        inv_p = 1.0 / self.PRICE_SCALE
        inv_s = 1.0 / self.SIZE_SCALE
        top_bid_keys = heapq.nlargest(3, self._bids_int.keys())
        top_ask_keys = heapq.nsmallest(3, self._asks_int.keys())
        bid_levels = [(k * inv_p, self._bids_int[k] * inv_s) for k in top_bid_keys]
        ask_levels = [(k * inv_p, self._asks_int[k] * inv_s) for k in top_ask_keys]
        bid_vol = sum((s for _, s in bid_levels))
        ask_vol = sum((s for _, s in ask_levels))
        total = bid_vol + ask_vol
        if total <= 0 or bid_vol <= 0 or ask_vol <= 0:
            return self.mid
        bid_vwap = sum((p * s for p, s in bid_levels)) / bid_vol
        ask_vwap = sum((p * s for p, s in ask_levels)) / ask_vol
        return (bid_vwap * ask_vol + ask_vwap * bid_vol) / total

    @property
    def top_depth_usdc(self) -> float:
        bbk = self._resolve_best_bid_key()
        bak = self._resolve_best_ask_key()
        bv = 0.0
        av = 0.0
        if bbk is not None:
            bv = bbk / self.PRICE_SCALE * (self._bids_int[bbk] / self.SIZE_SCALE)
        if bak is not None:
            av = bak / self.PRICE_SCALE * (self._asks_int[bak] / self.SIZE_SCALE)
        return bv + av

    @property
    def spread_pct(self) -> float:
        bb, ba = (self.best_bid, self.best_ask)
        if bb is not None and ba is not None and (bb > 0):
            return (ba - bb) / bb
        return 1.0

    @property
    def age_ms(self) -> float:
        """Local transport age (receipt â†’ now). Primary LatArb book-age metric."""
        return (time.monotonic() - self.ts) * 1000

    @property
    def exchange_age_ms(self) -> float:
        """Age of last venue timestamp vs wall clock; inf if unknown."""
        if self.exchange_ts_ms is None or self.exchange_ts_ms <= 0:
            return float('inf')
        return max(0.0, time.time() * 1000.0 - float(self.exchange_ts_ms))

    @property
    def is_crossed(self) -> bool:
        """True when best bid >= best ask (phantom / inconsistent book)."""
        bb, ba = (self.best_bid, self.best_ask)
        return bb is not None and ba is not None and bb >= ba

    def is_stale(self, max_ms: float) -> bool:
        """Stale if local transport age exceeds max, or known exchange age is wildly old (>5s)."""
        if self.age_ms > max_ms:
            return True
        ea = self.exchange_age_ms
        if math.isfinite(ea) and ea > max(max_ms, 5000.0):
            return True
        return False

@dataclass
class Position:
    shares: float = 0.0
    cost: float = 0.0

    @property
    def avg_price(self) -> float:
        return self.cost / self.shares if self.shares > 0 else 0.0

    def add(self, shares: float, cost: float) -> None:
        self.shares += shares
        self.cost += cost

    def reduce(self, shares: float) -> None:
        if self.shares <= 0:
            return
        n = min(shares, self.shares)
        avg = self.avg_price
        self.shares -= n
        self.cost = self.shares * avg

@dataclass
class Market:
    market_id: str
    question: str
    yes_token: str
    no_token: str
    condition_id: str = ''
    end_time: Optional[float] = None
    coin: Optional[str] = None
    tf_secs: int = 300
    book_yes: Optional[OrderBook] = None
    book_no: Optional[OrderBook] = None
    pos_yes: Position = field(default_factory=Position)
    pos_no: Position = field(default_factory=Position)
    liquidity: float = 0.0
    volatility: float = 0.0
    neg_risk: bool = False
    fees_enabled: bool = False
    # Polymarket feeRate coefficient (fee = rate * (p*(1-p))**exponent). None â†’ Config.category_fee_rate.
    fee_rate: Optional[float] = None
    fee_exponent: float = 1.0
    # Conditional-token share minimum from CLOB book (not USDC). None â†’ unenforced.
    min_order_size: Optional[float] = None
    tick_sizes: Dict[str, float] = field(default_factory=dict)
    _tick_decimals: Dict[str, int] = field(default_factory=dict)
    _tick_max_ticks: Dict[str, int] = field(default_factory=dict)
    latarb_hold: bool = False
    latarb_hold_tokens: Set[str] = field(default_factory=set)

    @property
    def is_crypto(self) -> bool:
        return self.coin is not None

    @property
    def ttc(self) -> Optional[float]:
        return self.end_time - time.time() if self.end_time else None

    @property
    def start_time(self) -> Optional[float]:
        if not self.end_time:
            return None
        return self.end_time - float(self.tf_secs)

    @property
    def total_cost(self) -> float:
        return self.pos_yes.cost + self.pos_no.cost

    def get_tick(self, token_id: str) -> float:
        return self.tick_sizes.get(token_id, 0.01)

    def set_tick(self, token_id: str, tick: float) -> None:
        if 0 < tick < 1:
            self.tick_sizes[token_id] = tick
            decimals = _tick_decimals(tick)
            self._tick_decimals[token_id] = decimals
            self._tick_max_ticks[token_id] = int(round(1.0 / tick)) - 1

    def tick_math(self, token_id: str) -> Tuple[int, int]:
        if token_id in self._tick_decimals:
            return (self._tick_decimals[token_id], self._tick_max_ticks[token_id])
        tick = self.get_tick(token_id)
        decimals = _tick_decimals(tick)
        max_ticks = int(round(1.0 / tick)) - 1
        self._tick_decimals[token_id] = decimals
        self._tick_max_ticks[token_id] = max_ticks
        return (decimals, max_ticks)

    def fresh_books(self, max_ms: float) -> bool:
        return self.book_yes is not None and (not self.book_yes.is_stale(max_ms)) and (self.book_no is not None) and (not self.book_no.is_stale(max_ms))

class PolyClient:

    def __init__(self, cfg: Config):
        self.cfg = cfg
        self.log = get_logger('PolyClient', cfg.log_level)
        self.session: Optional[aiohttp.ClientSession] = None
        self.sdk: Optional[Any] = None
        self.api_key = ''
        self.api_secret = ''
        self.api_passphrase = ''
        self.signer_address = ''
        self.trading_address = ''
        self.active_mode = ''
        self.lib_broken = False
        self._token_to_market: Dict[str, Market] = {}
        # One worker per coin for concurrent LatArb FAK sign+POST, plus headroom for directional.
        _n_coins = max(1, len(cfg.coins or []))
        self._order_pool = concurrent.futures.ThreadPoolExecutor(max_workers=max(4, _n_coins + 2), thread_name_prefix='order-io')

    def set_market_ref(self, t2m: Dict[str, Market]) -> None:
        self._token_to_market = t2m

    def close(self) -> None:
        self._order_pool.shutdown(wait=True, cancel_futures=True)

    def _persist_tick(self, token_id: str, tick: float) -> None:
        m = self._token_to_market.get(token_id)
        if m and 0 < tick < 1:
            old = m.tick_sizes.get(token_id)
            m.set_tick(token_id, tick)
            self.log.info('Tick updated  %s: %s -> %s', token_id[:16], old, tick)

    async def _build_sdk(self, sig_type: int) -> bool:
        if not _HAS_SDK:
            self.log.error('Polymarket SDK not installed â€” run: %s/bin/pip install py-clob-client-v2' % sys.prefix)
            return False
        if not _SDK_IS_V2:
            self.log.critical('Polymarket CLOB V1 SDK (py-clob-client) detected â€” CLOB V1 was retired 2026-04-28 and V1-signed orders are rejected with order_version_mismatch. Install the V2 SDK and restart:\n    %s/bin/pip install py-clob-client-v2' % sys.prefix)
            return False
        loop = asyncio.get_running_loop()
        label = _SIG_LABELS.get(sig_type, f'type_{sig_type}')
        try:
            kw: Dict[str, Any] = {'host': self.cfg.clob_url, 'chain_id': self.cfg.chain_id, 'key': self.cfg.private_key}
            if self.cfg.use_proxy and sig_type in (1, 2):
                kw['signature_type'] = sig_type
                kw['funder'] = self.cfg.proxy_address
            elif sig_type == 0:
                kw['signature_type'] = 0
            sdk = ClobClient(**kw)
            _derive = getattr(sdk, 'create_or_derive_api_key', None) or getattr(sdk, 'create_or_derive_api_creds', None)
            if _derive is None:
                raise RuntimeError('SDK exposes neither create_or_derive_api_key nor create_or_derive_api_creds â€” incompatible py-clob-client')
            creds = await loop.run_in_executor(None, _derive)
            sdk.set_api_creds(creds)
            self.sdk = sdk
            self.api_key = creds.api_key
            self.api_secret = creds.api_secret
            self.api_passphrase = creds.api_passphrase
            self.cfg.signature_type = sig_type
            self.trading_address = self.cfg.proxy_address or self.signer_address
            self.active_mode = f'sdk_{label}'
            self.log.info('SDK ready  sig_type=%d (%s)  trader=%s', sig_type, label, self.trading_address)
            return True
        except Exception as e:
            self.log.error('SDK build failed  sig_type=%d (%s): %s', sig_type, label, e)
            return False

    async def initialize(self, session: aiohttp.ClientSession) -> bool:
        self.session = session
        if self.cfg.dry_run and (not self.cfg.private_key):
            self.signer_address = ''
            self.trading_address = self.cfg.proxy_address or 'dry-run'
            self.active_mode = 'dry_run_no_key'
            self.log.warning('DRY_RUN with no private key: skipping SDK auth; orders are simulated only and user-fill WS is disabled')
            return True
        self.signer_address = Account.from_key(self.cfg.private_key).address
        self.log.info('Signer EOA: %s', self.signer_address)
        loop = asyncio.get_running_loop()
        try:
            on_chain = await asyncio.wait_for(loop.run_in_executor(None, lambda: _lookup_proxy_address(self.signer_address, self.cfg.chain_id)), timeout=8.0)
        except asyncio.TimeoutError:
            on_chain = None
            self.log.warning('Proxy lookup timed out â€” using .env value')
        if on_chain:
            if not self.cfg.proxy_address:
                self.log.info('Proxy not in .env â€” using on-chain value: %s', on_chain)
                self.cfg.proxy_address = on_chain
            elif self.cfg.proxy_address.lower() != on_chain.lower():
                self.log.warning('PROXY MISMATCH â€” .env=%s  on-chain=%s â€” auto-correcting.', self.cfg.proxy_address, on_chain)
                self.cfg.proxy_address = on_chain
            else:
                self.log.info('Proxy address verified on-chain: %s', on_chain)
        else:
            self.log.warning('Could not verify proxy address on-chain. Using .env: %s', self.cfg.proxy_address or '(none)')
        return await self._build_sdk(self.cfg.signature_type)

    async def test_order(self, token_id: str, tick_size: float=0.01, neg_risk: bool=False) -> bool:
        """Build and sign a representative order without posting it to the venue."""
        if not self.sdk:
            return False
        loop = asyncio.get_running_loop()
        test_price = snap_price(0.001, tick_size, 'BUY')
        try:
            args = OrderArgs(token_id=token_id, price=test_price, size=1.0, side=_SDK_BUY)
            try:
                opts = PartialCreateOrderOptions(neg_risk=neg_risk, tick_size=str(tick_size))
            except TypeError:
                opts = PartialCreateOrderOptions(neg_risk=neg_risk)
            signed = await loop.run_in_executor(None, lambda: self.sdk.create_order(args, opts))
            if signed is None:
                raise RuntimeError('SDK create_order returned no signed order')
            self.log.info('Offline signing test PASSED  sig_type=%d  neg_risk=%s (not posted)', self.cfg.signature_type, neg_risk)
            return True
        except Exception as e:
            self.log.warning('Offline signing test FAILED: %s', str(e)[:200])
            return False

    async def get_balance(self) -> Optional[float]:
        sdk_tried = False
        if self.sdk:
            try:
                loop = asyncio.get_running_loop()
                params = BalanceAllowanceParams(asset_type=AssetType.COLLATERAL if AssetType else 'COLLATERAL')
                resp = await loop.run_in_executor(None, self.sdk.get_balance_allowance, params)
                sdk_tried = True
                bal = _try_parse_balance_payload(resp)
                if bal is not None:
                    return bal
                self.log.warning('SDK balance payload missing/malformed balance field (type=%s keys=%s) â€” falling back to REST', type(resp).__name__, list(resp.keys())[:12] if isinstance(resp, dict) else None)
            except Exception as e:
                self.log.warning('SDK balance error (falling back to REST): %s', e)
        if self.cfg.proxy_address and self.session:
            try:
                qs = urlencode({'asset_type': 'COLLATERAL', 'address': self.cfg.proxy_address})
                path = f'/balance-allowance?{qs}'
                auth_hdrs = self._hmac_headers('GET', path)
                async with self.session.get(f'{self.cfg.clob_url}{path}', headers=auth_hdrs, timeout=aiohttp.ClientTimeout(total=5)) as r:
                    if r.ok:
                        d = await r.json(content_type=None)
                        bal = _try_parse_balance_payload(d)
                        if bal is not None:
                            return bal
                        self.log.warning('REST balance payload missing/malformed balance field (type=%s keys=%s)', type(d).__name__, list(d.keys())[:12] if isinstance(d, dict) else None)
                    else:
                        self.log.warning('REST balance HTTP %s â€” no authority', r.status)
            except Exception as e:
                self.log.warning('REST balance error: %s', e)
        self.log.warning('get_balance: no authoritative snapshot (sdk_tried=%s)', sdk_tried)
        return None

    @staticmethod
    def _parse_placement_response(resp: dict, side: 'Side') -> PlacementResult:
        oid = str(resp.get('orderID') or resp.get('id') or resp.get('order_id') or '')
        status = str(resp.get('status') or resp.get('orderStatus') or resp.get('order_status') or '').upper()
        matched = 0.0
        avg_px: Optional[float] = None
        scale = Decimal(10) ** 6
        sm_raw = None
        for k in ('size_matched', 'matchedSize', 'matched_size', 'filledSize', 'filled_size', 'sizeFilled'):
            if resp.get(k) is not None and str(resp.get(k)).strip() != '':
                sm_raw = resp[k]
                break
        if sm_raw is not None:
            try:
                matched = float(Decimal(str(sm_raw)))
            except (InvalidOperation, ValueError, TypeError):
                matched = 0.0
            for k in ('averagePrice', 'average_price', 'avgPrice', 'price'):
                if resp.get(k) is not None:
                    try:
                        px = float(Decimal(str(resp[k])))
                        if 0.0 < px < 1.0:
                            avg_px = px
                            break
                    except (InvalidOperation, ValueError, TypeError):
                        pass
        else:

            def _micro(key_primary: str, *alts: str) -> Decimal:
                for k in (key_primary,) + alts:
                    if resp.get(k) is None or str(resp.get(k)).strip() == '':
                        continue
                    try:
                        return Decimal(str(resp[k]))
                    except (InvalidOperation, ValueError, TypeError):
                        continue
                return Decimal(0)
            making = _micro('makingAmount', 'making_amount', 'makerAmount')
            taking = _micro('takingAmount', 'taking_amount', 'takerAmount')
            if isinstance(side, Side):
                is_buy = side == Side.BUY
            else:
                is_buy = str(side).upper() in ('BUY', 'B')
            if is_buy:
                shares_micro, collateral_micro = (taking, making)
            else:
                shares_micro, collateral_micro = (making, taking)
            if shares_micro > 0:
                matched = float(shares_micro / scale)
                if collateral_micro > 0:
                    try:
                        avg_px = float(collateral_micro / shares_micro)
                        if not 0.0 < avg_px < 1.0:
                            avg_px = None
                    except Exception:
                        avg_px = None
        return PlacementResult(order_id=oid, status=status, matched_size=max(0.0, matched), avg_fill_price=avg_px, raw=dict(resp))

    async def get_order(self, order_id: str) -> Optional[dict]:
        if not self.sdk or not order_id:
            return None
        try:
            loop = asyncio.get_running_loop()
            getter = getattr(self.sdk, 'get_order', None)
            if getter is None:
                return None
            resp = await loop.run_in_executor(None, getter, order_id)
            return resp if isinstance(resp, dict) else None
        except Exception as e:
            self.log.debug('get_order %s failed: %s', order_id[:12], e)
            return None

    async def list_open_orders(self) -> List[dict]:
        if not self.sdk:
            return []
        try:
            loop = asyncio.get_running_loop()
            _get_open = getattr(self.sdk, 'get_open_orders', None)
            if _get_open:
                live_list = await loop.run_in_executor(None, _get_open)
            else:
                live_list = await loop.run_in_executor(None, lambda: self.sdk.get_orders({'maker_address': self.trading_address, 'status': 'LIVE'}))
            return [o for o in live_list or [] if isinstance(o, dict)]
        except Exception as e:
            self.log.warning('list_open_orders failed: %s', e)
            raise

    async def place_order(self, token_id: str, side: str, price: float, size_usdc: float, order_type: str='GTC', neg_risk: bool=False, tick_size: float=0.01, expiration_s: float=0.0, post_only: bool=False) -> Optional[PlacementResult]:
        if not self.sdk:
            return None
        price = snap_price(price, tick_size, side)
        if side in ('BUY', Side.BUY):
            shares = round(size_usdc / max(price, 0.001), 6)
            if shares < 1.0:
                shares = 1.0
        else:
            shares = round(size_usdc / max(price, 0.001), 6)
            if shares < 1.0:
                shares = 1.0
        loop = asyncio.get_running_loop()
        side_enum = Side.BUY if side in ('BUY', Side.BUY) else Side.SELL
        sdk_side = _SDK_BUY if side_enum == Side.BUY else _SDK_SELL
        otype_u = (order_type or 'GTC').upper()
        exp_ts = 0
        live_maker = not self.cfg.dry_run and str(getattr(self.cfg, 'entry_mode', '')).lower() == 'maker'
        wants_gtd = otype_u == 'GTD' or (otype_u in ('GTC', 'GTD') and float(expiration_s or 0.0) > 0.0) or (live_maker and otype_u not in ('FOK', 'FAK'))
        if otype_u == 'FOK':
            ot = OrderType.FOK
        elif otype_u == 'FAK':
            ot = getattr(OrderType, 'FAK', None)
            if ot is None:
                raise RuntimeError('OrderType.FAK unavailable in SDK â€” upgrade py-clob-client-v2')
        elif wants_gtd:
            if not hasattr(OrderType, 'GTD'):
                raise RuntimeError('OrderType.GTD unavailable in SDK â€” refuse to post resting order without venue-backed expiry (no silent GTC downgrade)')
            ttl = float(expiration_s or 0.0)
            if live_maker and ttl < 120.0:
                ttl = max(ttl, float(getattr(self.cfg, 'maker_gtd_ttl_s', 120.0) or 120.0))
            if ttl < 120.0:
                raise RuntimeError(f'GTD requires effective ttl >= 120s (got {ttl}); Polymarket rejects exp < now+180s')
            ot = OrderType.GTD
            now_s = int(time.time())
            effective_ttl = max(120, int(math.ceil(ttl)))
            exp_ts = now_s + 60 + effective_ttl
            if exp_ts < now_s + 180:
                raise RuntimeError(f'GTD expiration violates Polymarket minimum (exp={exp_ts} < now+180={now_s + 180})')
            otype_u = 'GTD'
        else:
            if live_maker:
                raise RuntimeError('LIVE ENTRY_MODE=maker refuses bare GTC â€” set MAKER_GTD_TTL_S>=120 for venue-backed expiry')
            ot = OrderType.GTC
        if exp_ts > 0:
            try:
                args = OrderArgs(token_id=token_id, price=price, size=shares, side=sdk_side, expiration=exp_ts)
            except TypeError as e:
                raise RuntimeError('OrderArgs does not accept expiration= â€” refuse GTD (upgrade py-clob-client-v2; no GTC fallback)') from e
            got_exp = int(getattr(args, 'expiration', 0) or 0)
            if got_exp != exp_ts:
                raise RuntimeError(f'OrderArgs dropped expiration (wanted {exp_ts}, got {got_exp}) â€” refuse to sign mismatched GTD')
        else:
            try:
                args = OrderArgs(token_id=token_id, price=price, size=shares, side=sdk_side, expiration=0)
            except TypeError:
                args = OrderArgs(token_id=token_id, price=price, size=shares, side=sdk_side)
        try:
            opts = PartialCreateOrderOptions(neg_risk=neg_risk, tick_size=str(tick_size))
        except TypeError:
            opts = PartialCreateOrderOptions(neg_risk=neg_risk)
        try:
            # py-clob-client-v2 has NO create_order_async/post_order_async.
            # Prefer create_and_post_order (one sync call) in a worker so the
            # event loop stays free; fall back to create_order+post_order.
            use_post_only = bool(post_only) and ot not in (OrderType.FOK, getattr(OrderType, 'FAK', OrderType.FOK))
            sdk = self.sdk
            _ot = ot
            _args = args
            _opts = opts
            _use_po = use_post_only

            def _sign_and_post():
                cap = getattr(sdk, 'create_and_post_order', None)
                if cap is not None:
                    try:
                        return cap(_args, _opts, _ot, post_only=_use_po)
                    except TypeError:
                        try:
                            return cap(_args, _opts, _ot)
                        except TypeError:
                            pass
                signed = sdk.create_order(_args, _opts)
                try:
                    return sdk.post_order(signed, _ot, post_only=_use_po)
                except TypeError:
                    return sdk.post_order(signed, _ot)

            resp = await loop.run_in_executor(self._order_pool, _sign_and_post)
            if not isinstance(resp, dict):
                raise RuntimeError('Unexpected CLOB order response: %r' % (resp,))
            result = self._parse_placement_response(resp, side_enum)
            if not result.order_id:
                raise RuntimeError('CLOB did not return orderID: %s' % (resp.get('error') or resp,))
            if otype_u in ('FOK', 'FAK') and result.matched_size <= 0.0:
                detail = await self.get_order(result.order_id)
                if detail:
                    d2 = self._parse_placement_response(detail, side_enum)
                    if d2.matched_size > 0.0 or d2.status:
                        result = PlacementResult(order_id=result.order_id, status=d2.status or result.status, matched_size=d2.matched_size or result.matched_size, avg_fill_price=d2.avg_fill_price or result.avg_fill_price, raw={**result.raw, **d2.raw})
            return result
        except Exception as e:
            es = str(e)
            el = es.lower()
            if any((k in el for k in ('balance', 'insufficient', 'allowance'))):
                self.log.warning('Insufficient balance/allowance  token=%s', token_id[:16])
            elif any((k in el for k in ('invalid signature', 'bad signature', 'unauthorized', 'authentication failed'))):
                self.log.error('CLOB rejected signature  token=%s  sig_type=%d\n  Ensure POLYMARKET_PRIVATE_KEY owns the proxy wallet and\n  has been linked via polymarket.com.', token_id[:16], self.cfg.signature_type)
            else:
                self.log.error('Order failed: %s', es[:200])
            raise

    async def cancel(self, order_id: str) -> bool:
        if not self.sdk:
            return False
        try:
            _cancel_one = getattr(self.sdk, 'cancel_order', None)
            if _cancel_one:
                _payload = type('P', (), {'orderID': order_id})
                resp = await asyncio.get_running_loop().run_in_executor(None, _cancel_one, _payload)
            else:
                resp = await asyncio.get_running_loop().run_in_executor(None, self.sdk.cancel, order_id)
            if isinstance(resp, dict) and resp.get('not_canceled'):
                return False
            return True
        except Exception:
            return False

    async def cancel_all(self) -> None:
        if not self.sdk:
            return
        try:
            await asyncio.get_running_loop().run_in_executor(None, self.sdk.cancel_all)
        except Exception:
            raise

    def _hmac_headers(self, method: str, path: str, body: str='') -> dict:
        if not self.api_key:
            return {}
        ts = str(int(time.time()))
        msg = (ts + method + path + body).encode()
        try:
            secret = base64.urlsafe_b64decode(self.api_secret)
        except Exception:
            secret = self.api_secret.encode()
        sig = base64.urlsafe_b64encode(hmac.new(secret, msg, hashlib.sha256).digest()).decode()
        return {'POLY_ADDRESS': self.cfg.proxy_address or self.signer_address, 'POLY_SIGNATURE': sig, 'POLY_TIMESTAMP': ts, 'POLY_NONCE': '0', 'POLY_API_KEY': self.api_key, 'POLY_PASSPHRASE': self.api_passphrase}

class RateLimiter:

    def __init__(self, per_sec: int):
        self._interval = 1.0 / float(per_sec)
        self._next = time.monotonic()
        self._lock = asyncio.Lock()

    async def acquire(self) -> None:
        async with self._lock:
            now = time.monotonic()
            if self._next <= now:
                self._next = now + self._interval
                return
            wait = self._next - now
            self._next += self._interval
        await asyncio.sleep(wait)

class Metrics:

    def __init__(self):
        self._order_latencies: Deque[float] = deque(maxlen=500)
        self._fill_count = 0
        self._order_count = 0
        self._total_pnl = 0.0
        self.log = get_logger('Metrics')

    def record_order_latency(self, ms: float) -> None:
        self._order_latencies.append(ms)
        self._order_count += 1

    def record_fill(self) -> None:
        self._fill_count += 1

    def record_pnl(self, delta: float) -> None:
        self._total_pnl += delta

    def summary(self) -> dict:
        lats = list(self._order_latencies)
        if lats:
            lats.sort()
            n = len(lats)
            p50 = lats[min(n // 2, n - 1)]
            p95 = lats[max(0, math.ceil(n * 0.95) - 1)]
            p99 = lats[max(0, math.ceil(n * 0.99) - 1)] if n > 10 else p95
        else:
            p50 = p95 = p99 = 0.0
        return {'orders': self._order_count, 'fills': self._fill_count, 'pnl': round(self._total_pnl, 4), 'lat_p50_ms': round(p50, 1), 'lat_p95_ms': round(p95, 1), 'lat_p99_ms': round(p99, 1)}

class _OrderErrorClass(str, Enum):
    RATE_LIMIT = 'rate_limit'
    NETWORK = 'network'
    AUTH_FAILURE = 'auth'
    BALANCE = 'balance'
    REJECTION = 'rejection'

def _classify_order_error(exc: BaseException) -> _OrderErrorClass:
    s = str(exc).lower()
    if '429' in s or 'rate limit' in s or 'too many' in s:
        return _OrderErrorClass.RATE_LIMIT
    if any((k in s for k in ('timeout', 'connectionreset', 'connection reset', 'connection refused', 'eof', 'disconnected', 'temporarily unavailable', '503', '502', '504', '500', '425', 'too early', 'maintenance'))):
        return _OrderErrorClass.NETWORK
    if any((k in s for k in ('signature', 'unauthorized', 'authentication', 'invalid api', 'api key'))):
        return _OrderErrorClass.AUTH_FAILURE
    if any((k in s for k in ('balance', 'allowance', 'insufficient'))):
        return _OrderErrorClass.BALANCE
    return _OrderErrorClass.REJECTION

class OrderState(str, Enum):
    PENDING = 'pending'
    OPEN = 'open'
    FILLED = 'filled'
    CANCELLED = 'cancelled'

@dataclass(frozen=True)
class PlacementResult:
    order_id: str
    status: str
    matched_size: float
    avg_fill_price: Optional[float]
    raw: Dict[str, Any] = field(default_factory=dict)

@dataclass
class TrackedOrder:
    order_id: str
    token_id: str
    side: Side
    price: float
    size: float
    strategy: Strategy
    state: OrderState = OrderState.PENDING
    created: float = field(default_factory=time.monotonic)
    filled_size: float = 0.0
    avg_fill_price: float = 0.0

class OrderManager:

    def __init__(self, cfg: Config, client: PolyClient, metrics: Optional[Metrics]=None):
        self.cfg = cfg
        self.client = client
        self.log = get_logger('Orders', cfg.log_level)
        self._orders: Dict[str, TrackedOrder] = {}
        self._by_token: Dict[Tuple[str, Any], Any] = {}
        self._lock = asyncio.Lock()
        self._rl = RateLimiter(cfg.rate_limit)
        self._cancel_rl = RateLimiter(max(5, cfg.rate_limit // 2))
        # N8 FIX: IOC (FOK/FAK) fast path stays unthrottled up to this many
        # sends per rolling second; beyond that it falls back to the shared
        # limiter so a multi-coin burst cannot fire unbounded orders.
        self._ioc_send_ts: Deque[float] = deque(maxlen=64)
        self._ioc_burst_cap: int = max(4, int(cfg.rate_limit) // 2)
        self._rejects = 0
        self._metrics = metrics
        self._bg_tasks: Set[asyncio.Task] = set()
        self._seen_trade_ids: Set[str] = set()
        self._seen_trade_order: Deque[str] = deque(maxlen=50000)
        self._seen_trade_ids_cap: int = 50000
        self._last_trade_cursor_ts: float = time.time()
        self._first_reconcile_done: bool = False
        self._fill_replay_handler: Optional[Callable[[dict], Any]] = None
        self._fill_apply_error: str = ''
        self.on_fill_failure: Optional[Callable[[str], None]] = None
        self._reconcile_fills_lock = asyncio.Lock()
        # Per-strategy adverse EWMA so directional toxic fills do not throttle LatArb FOKs.
        self._adverse_ewma_by_strategy: Dict[str, float] = {}
        self._shadow_sink: Optional[Callable[[dict], Any]] = None
        # F9: durable-enough entry strategy tag (token_id -> 'latarb'|'directional')
        # so fill attribution does not depend only on volatile Market.latarb_hold*.
        self._entry_strategy_by_token: Dict[str, str] = {}

    def tag_entry_strategy(self, token_id: str, strategy: str) -> None:
        if token_id:
            self._entry_strategy_by_token[token_id] = strategy

    def get_entry_strategy(self, token_id: str) -> Optional[str]:
        return self._entry_strategy_by_token.get(token_id)

    def clear_entry_strategy(self, token_id: str) -> None:
        self._entry_strategy_by_token.pop(token_id, None)

    def set_shadow_sink(self, sink: Callable[[dict], Any]) -> None:
        self._shadow_sink = sink

    def record_adverse(self, adverse_bps: float, strategy: str='directional') -> None:
        key = (strategy or 'directional').lower()
        a = self.cfg.adverse_ewma_alpha
        prev = self._adverse_ewma_by_strategy.get(key)
        if prev is None:
            self._adverse_ewma_by_strategy[key] = adverse_bps
        else:
            self._adverse_ewma_by_strategy[key] = (1.0 - a) * prev + a * adverse_bps

    def adverse_ewma(self, strategy: str='directional') -> Optional[float]:
        return self._adverse_ewma_by_strategy.get((strategy or 'directional').lower())

    def set_fill_replay_handler(self, handler: Callable[[dict], Any]) -> None:
        self._fill_replay_handler = handler

    @property
    def fill_apply_error(self) -> str:
        return self._fill_apply_error

    def latch_fill_failure(self, reason: str) -> None:
        if not self._fill_apply_error:
            self._fill_apply_error = str(reason or 'unknown fill durability failure')
            self.log.critical('FILL DURABILITY LATCH: %s ? all new orders blocked', self._fill_apply_error)
            if self.on_fill_failure is not None:
                try:
                    self.on_fill_failure(self._fill_apply_error)
                except Exception as e:
                    self.log.critical('Could not checkpoint fill-durability halt: %s', e)

    def has_seen_trade(self, trade_id: str) -> bool:
        return bool(trade_id and trade_id in self._seen_trade_ids)

    def mark_trade_seen(self, trade_id: str) -> bool:
        if not trade_id:
            return False
        if trade_id in self._seen_trade_ids:
            return False
        if len(self._seen_trade_order) == self._seen_trade_ids_cap:
            evicted = self._seen_trade_order[0]
            self._seen_trade_ids.discard(evicted)
        self._seen_trade_order.append(trade_id)
        self._seen_trade_ids.add(trade_id)
        return True

    def spawn_fill_probe(self, token_id: str, side: Side, fill_price: float, fill_size: float=0.0, trade_id: str='') -> None:
        if not self.cfg.shadow_probe_enabled:
            return
        if not math.isfinite(fill_price) or not 0.0 < fill_price < 1.0:
            return
        mkt = self.client._token_to_market.get(token_id)
        if mkt is None:
            return
        book = mkt.book_yes if token_id == mkt.yes_token else mkt.book_no
        if book is None:
            return
        entry_mid = book.mid
        if entry_mid is None or entry_mid <= 0:
            return
        entry_spread = book.spread_pct
        fill_ts = time.monotonic()

        async def _probe() -> None:
            try:
                await asyncio.sleep(0.5)
                post_mid = book.mid
                if post_mid is None:
                    return
                adverse = entry_mid - post_mid if side == Side.BUY else post_mid - entry_mid
                adverse_bps = adverse / entry_mid * 10000.0
                strat_key = self.get_entry_strategy(token_id) or 'directional'
                self.record_adverse(adverse_bps, strategy=strat_key)
                self.log.info('SHADOW_FILL %s %s @ %.4f sz=%.4f tid=%s | entry_mid=%.4f post_mid=%.4f spread=%.4f adverse=%+.1fbps ewma=%+.1fbps strat=%s', side.value, token_id[:12], fill_price, fill_size, (trade_id or '-')[:16], entry_mid, post_mid, entry_spread, adverse_bps, self.adverse_ewma(strat_key) or 0.0, strat_key)
                if self._shadow_sink is not None:
                    try:
                        self._shadow_sink({'market_id': mkt.market_id, 'token_id': token_id, 'side': side.value, 'fill_price': fill_price, 'fill_size': fill_size, 'trade_id': trade_id, 'fill_ts_mono': fill_ts, 'adverse_bps': adverse_bps})
                    except Exception:
                        pass
            except Exception:
                pass
        try:
            t = asyncio.create_task(_probe(), name=f'shadow_{token_id[:8]}')
            self._bg_tasks.add(t)
            t.add_done_callback(self._bg_tasks.discard)
        except RuntimeError:
            pass

    def _spawn_shadow_probe(self, token_id: str, side: Side, fill_price: float) -> None:
        self.spawn_fill_probe(token_id, side, fill_price)

    async def place(self, token_id: str, side: Side, price: float, size: float, strategy: Strategy, otype: str='GTC', neg_risk: bool=False, tick_size: float=0.01, quote_ts: Optional[float]=None, max_quote_age_ms: Optional[float]=None) -> Optional[str]:
        try:
            asyncio.get_running_loop()
        except RuntimeError:
            return None
        if self._fill_apply_error:
            self.log.critical('ORDER BLOCKED by fill durability latch: %s', self._fill_apply_error)
            return None
        key = (token_id, side)
        reservation: object = object()
        committed = False
        async with self._lock:
            existing_oid = self._by_token.get(key)
            if existing_oid is not None:
                if not isinstance(existing_oid, str):
                    self.log.warning('DUP_GUARD: refusing %s %s â€” submission already pending', side.value, token_id[:12])
                    return None
                existing = self._orders.get(existing_oid)
                if existing is not None and existing.state in (OrderState.PENDING, OrderState.OPEN):
                    self.log.warning('DUP_GUARD: refusing %s %s â€” existing %s still %s', side.value, token_id[:12], existing_oid[:8], existing.state.value)
                    return None
            self._by_token[key] = reservation
        t0 = time.monotonic()

        async def _clear_if_ours() -> None:
            async with self._lock:
                if self._by_token.get(key) is reservation:
                    self._by_token.pop(key, None)

        async def _reject_if_quote_stale(stage: str) -> bool:
            if quote_ts is None or max_quote_age_ms is None or max_quote_age_ms <= 0:
                return False
            age_ms = (time.monotonic() - quote_ts) * 1000.0
            if age_ms <= max_quote_age_ms:
                return False
            self.log.info('STALE_QUOTE_REJECT %s %s %s age=%.0fms max=%.0fms', stage, side.value, token_id[:12], age_ms, max_quote_age_ms)
            return True
        try:
            if side == Side.BUY:
                mkt_ref = self.client._token_to_market.get(token_id)
                if mkt_ref is not None:
                    pos = mkt_ref.pos_yes if token_id == mkt_ref.yes_token else mkt_ref.pos_no
                    if pos.shares > 1e-06:
                        self.log.debug('STP: skipping BUY %s â€” already hold %.6f shares', token_id[:12], pos.shares)
                        return None
            if self.cfg.dry_run:
                await asyncio.sleep(self.cfg.dry_run_latency_ms / 1000.0)
                if await _reject_if_quote_stale('dry-run'):
                    return None
                otype_u_dry = (otype or 'GTC').upper()
                dry_fill_price = price
                matched_shares = 0.0
                mkt_ref = self.client._token_to_market.get(token_id)
                book_ref = None
                if mkt_ref is not None:
                    book_ref = mkt_ref.book_yes if token_id == mkt_ref.yes_token else mkt_ref.book_no
                if otype_u_dry in ('FOK', 'FAK') and side == Side.BUY:
                    # P1: match live FAK â€” request shares = USDC/limit, depth-walk only asks <= limit.
                    req_shares = size / max(price, 0.001)
                    if book_ref is not None and hasattr(book_ref, 'asks'):
                        rem = req_shares
                        cost = 0.0
                        got = 0.0
                        for ap, az in list(book_ref.asks or []):
                            if ap is None or az is None or ap <= 0 or az <= 0:
                                continue
                            if float(ap) > float(price) + 1e-12:
                                break
                            take = min(float(az), rem)
                            cost += take * float(ap)
                            got += take
                            rem -= take
                            if rem <= 1e-12:
                                break
                        if got > 1e-12 and cost > 0:
                            matched_shares = round(got, 6)
                            dry_fill_price = cost / got
                        elif otype_u_dry == 'FOK':
                            matched_shares = 0.0
                    # Optional residual RNG only if book empty (legacy dry probe)
                    if matched_shares <= 0 and book_ref is None and random.random() < self.cfg.dry_run_fill_prob:
                        matched_shares = round(req_shares, 6)
                        dry_fill_price = price
                elif otype_u_dry in ('FOK', 'FAK') and side == Side.SELL:
                    req_shares = size / max(price, 0.001)
                    if book_ref is not None and mkt_ref is not None:
                        _dec, _mt = mkt_ref.tick_math(token_id)
                        entry_vwap = _fok_sweep_price_sell(book_ref, req_shares, tick_size, _dec, _mt)
                        if entry_vwap > 0 and math.isfinite(entry_vwap):
                            matched_shares = round(req_shares, 6)
                            dry_fill_price = entry_vwap
                else:
                    if random.random() < self.cfg.dry_run_fill_prob:
                        matched_shares = round(size / max(price, 0.001), 6)
                        dry_fill_price = price
                filled = matched_shares > 1e-12
                elapsed_ms = (time.monotonic() - t0) * 1000
                oid = f'dry-{int(time.time() * 1000)}' if filled else None
                self.log.info('DRY %s %s limit=%.4f fill_px=%.4f sh=%.4f $%.2f [%s] fill=%s %.1fms', side.value, token_id[:12], price, dry_fill_price, matched_shares, size, strategy.value, filled, elapsed_ms)
                if self._metrics:
                    self._metrics.record_order_latency(elapsed_ms)
                if not oid:
                    return None
                shares = matched_shares
                if shares <= 0:
                    return None
                async with self._lock:
                    self._orders[oid] = TrackedOrder(oid, token_id, side, price, size, strategy, state=OrderState.FILLED, filled_size=shares, avg_fill_price=dry_fill_price)
                    self._by_token[key] = oid
                    committed = True
                if self._fill_replay_handler is not None:
                    try:
                        payload = {'asset_id': token_id, 'side': side.value, 'price': str(dry_fill_price), 'size': str(shares), 'trade_id': oid, 'order_id': oid, '_ioc_aggregate': otype_u_dry in ('FOK', 'FAK')}
                        res = self._fill_replay_handler(payload)
                        if asyncio.iscoroutine(res):
                            await res
                    except Exception as e:
                        self.latch_fill_failure(f'dry fill {oid} apply failed: {e}')
                    else:
                        self.mark_trade_seen(oid)
                return oid
            otype_u = (otype or 'GTC').upper()
            # LatArb FOKs/FAKs are rare and time-critical â€” skip shared rate limiter.
            if otype_u not in ('FOK', 'FAK'):
                await self._rl.acquire()
            else:
                # N8 FIX: bounded fast path — normal signal cadence (max 5
                # concurrent evals) never waits here; only a runaway burst does.
                _now_mono = time.monotonic()
                self._ioc_send_ts.append(_now_mono)
                if sum(1 for _t in self._ioc_send_ts if _now_mono - _t <= 1.0) > self._ioc_burst_cap:
                    self.log.warning('IOC burst > %d/s — falling back to shared rate limiter', self._ioc_burst_cap)
                    await self._rl.acquire()
            if await _reject_if_quote_stale('live'):
                return None
            expiration_s = 0.0
            post_only = False
            live_maker = not self.cfg.dry_run and self.cfg.entry_mode == 'maker'
            if otype_u not in ('FOK', 'FAK'):
                if live_maker:
                    if self.cfg.maker_gtd_ttl_s < 120.0:
                        self.log.error('LIVE maker refuses resting order: MAKER_GTD_TTL_S=%.1f < 120', self.cfg.maker_gtd_ttl_s)
                        return None
                    otype_u = 'GTD'
                    expiration_s = float(self.cfg.maker_gtd_ttl_s)
                    post_only = True
                elif self.cfg.maker_gtd_ttl_s >= 120.0:
                    otype_u = 'GTD'
                    expiration_s = float(self.cfg.maker_gtd_ttl_s)
                    post_only = self.cfg.entry_mode == 'maker'
            try:
                pr = await self.client.place_order(token_id, side.value, price, size, otype_u, neg_risk, tick_size, expiration_s=expiration_s, post_only=post_only)
            except Exception as e:
                ec = _classify_order_error(e)
                if ec == _OrderErrorClass.RATE_LIMIT:
                    self.log.debug('rate-limit slot consumed (will recover via 1s sleep)')
                    await asyncio.sleep(1.0)
                elif ec == _OrderErrorClass.NETWORK:
                    self.log.debug('network slot consumed (transient: %s)', str(e)[:80])
                else:
                    async with self._lock:
                        self._rejects += 1
                self.log.error('Order %s: %s', ec.value, str(e)[:120])
                return None
            elapsed_ms = (time.monotonic() - t0) * 1000
            if self._metrics:
                self._metrics.record_order_latency(elapsed_ms)
            if pr is None or not pr.order_id:
                return None
            oid = pr.order_id
            matched = float(pr.matched_size or 0.0)
            avg_px = pr.avg_fill_price
            status_u = (pr.status or '').upper()
            is_ioc = otype_u in ('FOK', 'FAK')
            exec_now = matched > 0.0 and avg_px is not None and (0.0 < float(avg_px) < 1.0) or status_u in ('MATCHED', 'FILLED', 'CLOSED')
            state = OrderState.OPEN
            if is_ioc and (not exec_now):
                state = OrderState.PENDING
            elif exec_now and matched > 0.0:
                state = OrderState.FILLED
            async with self._lock:
                self._orders[oid] = TrackedOrder(oid, token_id, side, price, size, strategy, state=state, filled_size=matched if exec_now else 0.0, avg_fill_price=float(avg_px or 0.0) if exec_now else 0.0)
                self._by_token[key] = oid
                self._rejects = 0
                committed = True
            self.log.info('%s %s %s @ %.4f  $%.2f  [%s]  status=%s matched=%.4f  %.1fms', otype_u, side.value, token_id[:12], price, size, strategy.value, status_u or '-', matched, elapsed_ms)
            if exec_now and matched > 0.0 and self._fill_replay_handler is not None:
                fill_px = float(avg_px) if avg_px and avg_px > 0 else price
                shares_fill = round(matched, 6)
                expected_sh = size / max(fill_px, 0.001)
                if shares_fill > max(expected_sh * 2.0, expected_sh + 1.0):
                    self.log.error('%s matched_size absurd oid=%s matched=%.6f expected~%.6f ? refusing immediate credit; REST reconcile only', otype_u, oid[:12], shares_fill, expected_sh)
                    shares_fill = 0.0
                if shares_fill > 0 and is_ioc:
                    trade_id = f'{otype_u.lower()}-{oid}'
                    try:
                        payload = {'asset_id': token_id, 'side': side.value, 'price': str(fill_px), 'size': str(shares_fill), 'trade_id': trade_id, 'order_id': oid, '_ioc_aggregate': True}
                        res = self._fill_replay_handler(payload)
                        if asyncio.iscoroutine(res):
                            await res
                    except Exception as e:
                        self.latch_fill_failure(f'immediate IOC fill {oid} apply failed: {e}')
                        self.log.critical('Immediate IOC fill left unacknowledged oid=%s: %s', oid[:12], e)
                    else:
                        self.mark_trade_seen(trade_id)
                        self.mark_trade_seen(oid)
                elif shares_fill > 0:
                    # Resting orders may receive multiple trades under one order id;
                    # wait for a venue trade id rather than creating a synthetic ack.
                    self.log.info('%s immediate match oid=%s deferred to WS/REST trade-id reconciliation', otype_u, oid[:12])
                    try:
                        await self.reconcile_fills(wait_if_busy=True)
                    except Exception as e:
                        self.latch_fill_failure(f'post-match reconciliation failed for {oid}: {e}')
            elif is_ioc:
                self.log.info('%s_ACCEPT %s %s oid=%s status=%s matched=0 ? REST reconcile before declaring a miss', otype_u, side.value, token_id[:12], oid[:12], status_u or '-')
                try:
                    await self.reconcile_fills(wait_if_busy=True)
                except Exception as e:
                    self.latch_fill_failure(f'post-{otype_u} reconciliation failed for {oid}: {e}')
                async with self._lock:
                    tracked = self._orders.get(oid)
                    matched = float(tracked.filled_size) if tracked is not None else 0.0
                    avg_px = float(tracked.avg_fill_price) if tracked is not None else 0.0
            # FAK/FOK: order acceptance â‰  fill. Zero matched_size is a miss (Polymarket FAK = fill-and-kill remainder).
            if is_ioc:
                async with self._lock:
                    tracked = self._orders.get(oid)
                    final_matched = float(tracked.filled_size) if tracked is not None else float(matched or 0.0)
                    if final_matched <= 1e-12:
                        self._orders.pop(oid, None)
                        if self._by_token.get(key) == oid:
                            self._by_token.pop(key, None)
                        committed = False
                        self.log.info('%s_NO_FILL %s %s oid=%s status=%s', otype_u, side.value, token_id[:12], oid[:12], status_u or '-')
                        return None
            return oid
        except asyncio.CancelledError:
            raise
        finally:
            if not committed:
                await _clear_if_ours()

    async def reconcile(self) -> int:
        if not self.client.sdk:
            return 0
        try:
            loop = asyncio.get_running_loop()
            _get_open = getattr(self.client.sdk, 'get_open_orders', None)
            if _get_open:
                live_list = await loop.run_in_executor(None, _get_open)
            else:
                live_list = await loop.run_in_executor(None, lambda: self.client.sdk.get_orders({'maker_address': self.client.trading_address, 'status': 'LIVE'}))
            live_index: Dict[str, dict] = {o.get('id') or o.get('orderID', ''): o for o in live_list or [] if isinstance(o, dict)}
        except Exception as e:
            self.log.debug('Reconcile fetch: %s', e)
            return 0
        pruned = 0
        now = time.monotonic()
        async with self._lock:
            for oid, tracked in list(self._orders.items()):
                if oid in live_index:
                    if tracked.state == OrderState.PENDING:
                        tracked.state = OrderState.OPEN
                    raw = live_index[oid]
                    new_filled = float(raw.get('size_matched') or raw.get('filledSize') or raw.get('takerAmount', 0) or 0)
                    if new_filled > tracked.filled_size:
                        prev = tracked.filled_size
                        delta = new_filled - prev
                        fp = float(raw.get('price', tracked.price) or tracked.price)
                        tracked.avg_fill_price = (tracked.avg_fill_price * prev + fp * delta) / new_filled if prev > 0 else fp
                        tracked.filled_size = new_filled
                else:
                    if tracked.state == OrderState.FILLED:
                        self._by_token.pop((tracked.token_id, tracked.side), None)
                        del self._orders[oid]
                        pruned += 1
                        continue
                    if tracked.filled_size > 0:
                        self.log.warning('Reconcile: pruning order %s with %.4f filled (WS may have missed partial fill - position may desync)', oid[:16], tracked.filled_size)
                    if tracked.state == OrderState.OPEN or now - tracked.created > 15:
                        self._by_token.pop((tracked.token_id, tracked.side), None)
                        del self._orders[oid]
                        pruned += 1
        if pruned:
            self.log.info('Reconcile: pruned %d stale orders (%d remaining)', pruned, len(self._orders))
        async with self._lock:
            if self._rejects > 0:
                self.log.info('Reconcile OK â€” clearing stale reject count (%d)', self._rejects)
                self._rejects = 0
        return pruned

    async def reconcile_fills(self, wait_if_busy: bool = False) -> int:
        if not self.client.sdk or self._fill_replay_handler is None or self.cfg.dry_run:
            return 0
        # C1 FIX: order-critical callers (place() post-FAK check) must not be
        # silently skipped just because the 30s background pass holds the lock;
        # they pass wait_if_busy=True and queue behind it.  The background loop
        # keeps skip semantics so passes never pile up.
        if self._reconcile_fills_lock.locked() and not wait_if_busy:
            return 0
        async with self._reconcile_fills_lock:
            first_pass = not self._first_reconcile_done
            since_ts = max(0.0, self._last_trade_cursor_ts - 3600.0) if first_pass else self._last_trade_cursor_ts
            if first_pass:
                self.log.info('reconcile_fills: first pass ? walking back to %.0f (%.0fs before boot)', since_ts, self._last_trade_cursor_ts - since_ts)
            try:
                trades = await self._fetch_trades_since(since_ts)
            except Exception as e:
                self.log.warning('reconcile_fills fetch error: %s', e)
                return 0
            replayed = 0
            max_ts = since_ts
            ordered = sorted((tr for tr in trades if isinstance(tr, dict)), key=lambda tr: (self._extract_trade_ts(tr), self._extract_trade_id(tr)))
            for tr in ordered:
                tid = self._extract_trade_id(tr)
                ts = self._extract_trade_ts(tr)
                if not tid:
                    reason = f'REST trade payload has no durable id: {tr!r}'
                    self.latch_fill_failure(reason)
                    raise RuntimeStateError(reason)
                if self.has_seen_trade(tid):
                    max_ts = max(max_ts, ts)
                    continue
                try:
                    result = self._fill_replay_handler(tr)
                    if asyncio.iscoroutine(result):
                        result = await result
                except Exception as e:
                    reason = f'REST fill {tid} apply/checkpoint failed: {e}'
                    self.latch_fill_failure(reason)
                    self.log.error('reconcile_fills: %s', reason)
                    # Do not acknowledge this id or advance the cursor.  Previously
                    # applied rows are durable and will dedupe on the next pass.
                    raise RuntimeStateError(reason) from e
                self.mark_trade_seen(tid)
                max_ts = max(max_ts, ts)
                if result is not False:
                    replayed += 1
                    self.log.warning('reconcile_fills: REPLAYED trade %s (WS likely missed it)', tid[:16])
            self._first_reconcile_done = True
            floor_ts = time.time() - 2.0 * max(5.0, self.cfg.reconcile_fills_interval_s)
            self._last_trade_cursor_ts = max(max_ts, floor_ts)
            if replayed:
                self.log.info('reconcile_fills: replayed %d missing fills (cursor=%.3f)', replayed, self._last_trade_cursor_ts)
            return replayed

    async def _fetch_trades_since(self, since_ts: float) -> List[dict]:
        loop = asyncio.get_running_loop()
        sdk = self.client.sdk
        since_int = int(since_ts)

        def _try() -> List[dict]:
            _get = getattr(sdk, 'get_trades', None)
            if _get is None:
                # C3 FIX (residual): never degrade silently — REST fill
                # reconciliation is a live-safety layer; if this SDK build cannot
                # serve it, say so loudly once instead of no-opping forever.
                if not getattr(self, '_warned_no_get_trades', False):
                    self._warned_no_get_trades = True
                    self.log.critical('SDK has no get_trades — REST fill reconciliation is DISABLED on this build; WS is the only fill source')
                return []
            try:
                from py_clob_client_v2.clob_types import TradeParams as _TradeParams
            except ImportError:
                try:
                    from py_clob_client.clob_types import TradeParams as _TradeParams
                except ImportError:
                    _TradeParams = None
            if _TradeParams is not None:
                params = _TradeParams(after=since_int, maker_address=self.client.trading_address)
            else:
                params = None
            try:
                if params is not None:
                    res = _get(params)
                else:
                    res = _get()
                if isinstance(res, dict):
                    res = res.get('data') or res.get('trades') or []
                if isinstance(res, list):
                    return res
            except Exception:
                raise
            return []
        return await loop.run_in_executor(None, _try)

    @staticmethod
    def _extract_trade_order_ids(tr: dict) -> Set[str]:
        ids: Set[str] = set()
        for key in ('order_id', 'orderId', 'taker_order_id', 'takerOrderId', 'maker_order_id', 'makerOrderId'):
            value = tr.get(key)
            if value:
                ids.add(str(value))
        for key in ('maker_orders', 'makerOrders', 'orders'):
            rows = tr.get(key)
            if not isinstance(rows, list):
                continue
            for row in rows:
                if not isinstance(row, dict):
                    continue
                for subkey in ('order_id', 'orderId', 'id'):
                    if row.get(subkey):
                        ids.add(str(row[subkey]))
        return ids

    @staticmethod
    def _extract_trade_id(tr: dict) -> str:
        return str(tr.get('trade_id') or tr.get('tradeId') or tr.get('id') or tr.get('transaction_hash') or '')

    @staticmethod
    def _extract_trade_ts(tr: dict) -> float:
        for key in ('match_time', 'timestamp', 'matchTime', 'ts'):
            v = tr.get(key)
            if v is None:
                continue
            try:
                f = float(v)
            except (TypeError, ValueError):
                continue
            if not math.isfinite(f) or f <= 0:
                continue
            if f > 1e+18:
                continue
            iters = 0
            while f > 100000000000.0 and iters < 5:
                f /= 1000.0
                iters += 1
            return f
        return 0.0

    async def cancel(self, oid: str) -> bool:
        await self._cancel_rl.acquire()
        ok = await self.client.cancel(oid)
        if ok:
            async with self._lock:
                tracked = self._orders.pop(oid, None)
                if tracked:
                    self._by_token.pop((tracked.token_id, tracked.side), None)
        return ok

    async def cancel_all(self) -> None:
        async with self._lock:
            snapshot_count = len(self._orders)
            snapshot_ids = list(self._orders.keys())
        if snapshot_count == 0:
            return
        try:
            await self.client.cancel_all()
        except Exception as e:
            self.log.error('cancel_all: exchange call failed (%s) â€” %d orders may remain open: %s', e, snapshot_count, ', '.join((oid[:8] for oid in snapshot_ids[:5])))
            raise
        async with self._lock:
            self._orders.clear()
            self._by_token.clear()
        self.log.info('cancel_all: confirmed %d orders cancelled', snapshot_count)

    async def cancel_open_buys(self) -> int:
        async with self._lock:
            buy_oids = [oid for oid, tracked in self._orders.items() if tracked.side == Side.BUY]
        if not buy_oids:
            return 0
        cancelled = 0
        for oid in buy_oids:
            try:
                if await self.cancel(oid):
                    cancelled += 1
            except Exception as e:
                self.log.warning('cancel_open_buys: failed %s: %s', oid[:12], e)
        self.log.info('cancel_open_buys: cancelled %d/%d resting BUY orders', cancelled, len(buy_oids))
        return cancelled

    def find_open(self, token_id: str, side: Side) -> Optional[TrackedOrder]:
        oid = self._by_token.get((token_id, side))
        if not isinstance(oid, str) or not oid:
            return None
        return self._orders.get(oid)

    def remove(self, oid: str) -> None:
        tracked = self._orders.pop(oid, None)
        if tracked:
            self._by_token.pop((tracked.token_id, tracked.side), None)

    @property
    def count(self) -> int:
        return sum((1 for o in self._orders.values() if o.state in (OrderState.PENDING, OrderState.OPEN)))

    @property
    def rejects(self) -> int:
        return self._rejects

class BinanceFeed:

    def __init__(self, coins: List[str]):
        self._coins = coins
        self._prices: Dict[str, float] = {}
        self._price_ts: Dict[str, float] = {}
        self._exchange_ts_ms: Dict[str, int] = {}
        self._cbs: List[Callable] = []
        self._running = False
        self._last_msg: float = 0.0
        self._ws: Optional[Any] = None
        self.log = get_logger('Binance')

    def price(self, coin: str, max_age_s: Optional[float]=None) -> Optional[float]:
        coin = coin.upper()
        if max_age_s is not None and self.price_age_s(coin) > max_age_s:
            return None
        return self._prices.get(coin)

    def price_age_s(self, coin: str) -> float:
        ts = self._price_ts.get(coin.upper(), 0.0)
        return time.monotonic() - ts if ts else float('inf')

    def on_update(self, cb: Callable) -> None:
        self._cbs.append(cb)

    async def run(self) -> None:
        self._running = True
        # aggTrade: same last price as @trade, far fewer messages (less loop pressure).
        streams = '/'.join((f'{c.lower()}usdt@aggTrade' for c in self._coins))
        url = f'wss://stream.binance.com:9443/stream?streams={streams}'
        backoff = 1.0
        while self._running:
            try:
                async with websockets.connect(url, ping_interval=20, ping_timeout=5, compression=None) as ws:
                    self._ws = ws
                    backoff = 1.0
                    self.log.info('Connected: %s', ', '.join(self._coins))
                    while self._running:
                        try:
                            msg = await asyncio.wait_for(ws.recv(), timeout=10.0)
                        except asyncio.TimeoutError as exc:
                            raise ConnectionError('Binance stream silent for 10s') from exc
                        now_mono = time.monotonic()
                        self._last_msg = now_mono
                        try:
                            d = _json_loads(msg).get('data', {})
                            sym = d.get('s', '').replace('USDT', '')
                            p = float(d.get('p', 0))
                            evt_ms = int(d.get('E') or d.get('T') or int(time.time() * 1000))
                        except (ValueError, TypeError, AttributeError) as e:
                            self.log.debug('BinanceFeed parse error: %s', e)
                            continue
                        if not sym or not math.isfinite(p) or p <= 0:
                            continue
                        prev_evt = self._exchange_ts_ms.get(sym, 0)
                        if prev_evt and evt_ms + 250 < prev_evt:
                            self.log.debug('Binance stale trade dropped %s evt=%d prev=%d', sym, evt_ms, prev_evt)
                            continue
                        if int(time.time() * 1000) - evt_ms > 5000:
                            self.log.debug('Binance delayed trade dropped %s evt=%d', sym, evt_ms)
                            continue
                        self._exchange_ts_ms[sym] = max(prev_evt, evt_ms)
                        self._prices[sym] = p
                        self._price_ts[sym] = now_mono
                        for cb in self._cbs:
                            try:
                                await cb(sym, p)
                            except Exception as cb_err:
                                self.log.debug('BinanceFeed cb error: %s', cb_err)
            except asyncio.CancelledError:
                self._ws = None
                break
            except Exception as e:
                self._ws = None
                if self._running:
                    self.log.warning('WS error: %s (retry in %.0fs)', e, backoff)
                    await asyncio.sleep(backoff * 0.5 + random.uniform(0.0, backoff * 0.5))
                    backoff = min(backoff * 2, 30)

    @property
    def last_msg_age_s(self) -> float:
        return time.monotonic() - self._last_msg if self._last_msg else float('inf')

    async def restart(self) -> None:
        ws = self._ws
        if ws is not None:
            try:
                await ws.close()
            except Exception:
                pass

    async def stop(self) -> None:
        self._running = False
        await self.restart()


class ChainlinkFeed:
    """Polymarket RTDS Chainlink prices â€” settlement oracle for 5m/15m crypto markets."""

    WS_URL = 'wss://ws-live-data.polymarket.com'

    def __init__(self, coins: List[str]):
        self._coins = [c.upper() for c in coins]
        self._prices: Dict[str, float] = {}
        self._price_ts: Dict[str, float] = {}
        self._exchange_ts_ms: Dict[str, int] = {}
        self._cbs: List[Callable] = []
        self._running = False
        self._last_msg: float = 0.0
        self._ws: Optional[Any] = None
        self.log = get_logger('Chainlink')

    def price(self, coin: str, max_age_s: Optional[float]=None) -> Optional[float]:
        coin = coin.upper()
        if max_age_s is not None and self.price_age_s(coin) > max_age_s:
            return None
        return self._prices.get(coin)

    def price_age_s(self, coin: str) -> float:
        ts = self._price_ts.get(coin.upper(), 0.0)
        return time.monotonic() - ts if ts else float('inf')

    def on_update(self, cb: Callable) -> None:
        self._cbs.append(cb)

    def _coin_from_symbol(self, symbol: str) -> Optional[str]:
        s = (symbol or '').strip().lower().replace('-', '/')
        if '/' in s:
            base = s.split('/', 1)[0].upper()
        elif s.endswith('usd') and len(s) > 3:
            base = s[:-3].upper()
        else:
            base = s.upper()
        return base if base in self._coins else None

    async def run(self) -> None:
        self._running = True
        sub = {'action': 'subscribe', 'subscriptions': [{'topic': 'crypto_prices_chainlink', 'type': '*', 'filters': ''}]}
        backoff = 1.0
        while self._running:
            try:
                async with websockets.connect(self.WS_URL, ping_interval=None, ping_timeout=None, compression=None) as ws:
                    self._ws = ws
                    backoff = 1.0
                    await ws.send(json.dumps(sub))
                    self.log.info('Connected RTDS Chainlink: %s', ', '.join(self._coins))
                    last_ping = time.monotonic()
                    while self._running:
                        try:
                            msg = await asyncio.wait_for(ws.recv(), timeout=5.0)
                        except asyncio.TimeoutError:
                            if time.monotonic() - last_ping >= 5.0:
                                try:
                                    await ws.send('PING')
                                except Exception:
                                    raise ConnectionError('Chainlink RTDS ping failed')
                                last_ping = time.monotonic()
                            continue
                        now_mono = time.monotonic()
                        if isinstance(msg, bytes):
                            msg = msg.decode('utf-8', errors='ignore')
                        if not msg or msg.strip().upper() in ('PONG', 'PING'):
                            continue
                        self._last_msg = now_mono
                        try:
                            d = _json_loads(msg)
                        except Exception:
                            continue
                        if not isinstance(d, dict):
                            continue
                        topic = str(d.get('topic') or '')
                        if topic and topic != 'crypto_prices_chainlink':
                            continue
                        payload = d.get('payload') or d
                        if not isinstance(payload, dict):
                            continue
                        sym = payload.get('symbol') or payload.get('Symbol') or ''
                        coin = self._coin_from_symbol(str(sym))
                        if not coin:
                            continue
                        try:
                            p = float(payload.get('value') or payload.get('price') or 0)
                            evt_ms = int(payload.get('timestamp') or d.get('timestamp') or int(time.time() * 1000))
                        except (ValueError, TypeError):
                            continue
                        if not math.isfinite(p) or p <= 0:
                            continue
                        prev_evt = self._exchange_ts_ms.get(coin, 0)
                        if prev_evt and evt_ms + 250 < prev_evt:
                            continue
                        if int(time.time() * 1000) - evt_ms > 15000:
                            continue
                        self._exchange_ts_ms[coin] = max(prev_evt, evt_ms)
                        self._prices[coin] = p
                        self._price_ts[coin] = now_mono
                        for cb in self._cbs:
                            try:
                                await cb(coin, p)
                            except Exception as cb_err:
                                self.log.debug('ChainlinkFeed cb error: %s', cb_err)
                        if time.monotonic() - last_ping >= 5.0:
                            try:
                                await ws.send('PING')
                            except Exception:
                                raise ConnectionError('Chainlink RTDS ping failed')
                            last_ping = time.monotonic()
            except asyncio.CancelledError:
                self._ws = None
                break
            except Exception as e:
                self._ws = None
                if self._running:
                    self.log.warning('WS error: %s (retry in %.0fs)', e, backoff)
                    await asyncio.sleep(backoff * 0.5 + random.uniform(0.0, backoff * 0.5))
                    backoff = min(backoff * 2, 30)

    @property
    def last_msg_age_s(self) -> float:
        return time.monotonic() - self._last_msg if self._last_msg else float('inf')

    async def restart(self) -> None:
        ws = self._ws
        if ws is not None:
            try:
                await ws.close()
            except Exception:
                pass

    async def stop(self) -> None:
        self._running = False
        await self.restart()


def _ws_exchange_ts_ms(msg: Any) -> Optional[int]:
    """Extract venue timestamp (ms) from a Polymarket market WS payload if present."""
    if not isinstance(msg, dict):
        return None
    for k in ('timestamp', 'timestamp_ms', 'ts', 'time', 'T', 't'):
        raw = msg.get(k)
        if raw is None or raw == '':
            continue
        try:
            v = float(raw)
        except (TypeError, ValueError):
            continue
        if not math.isfinite(v) or v <= 0:
            continue
        # Seconds epoch â†’ ms
        if v < 1e12:
            v *= 1000.0
        return int(v)
    return None

class HyperPolyFeed:
    WS_URL = 'wss://ws-subscriptions-clob.polymarket.com/ws/market'
    TRADE_ALPHA = 0.3
    TRADE_TTL = 30.0

    def __init__(self, shard_count: int=2) -> None:
        self._books: Dict[str, OrderBook] = {}
        self._tokens: List[str] = []
        self._token_set: Set[str] = set()
        self._cbs: List[Callable] = []
        self._resolved_cb: Optional[Callable] = None
        self._trade_ewma: Dict[str, float] = {}
        self._trade_ts: Dict[str, float] = {}
        self._last_large_trade_ts: Dict[str, float] = {}
        self._whale_threshold_usdc: float = 0.0
        self._last_msgs: Dict[int, float] = {}
        self._ws_shards: Dict[int, Any] = {}
        self._shard_count = max(1, shard_count)
        self._running = False
        self._snapshot_received: Set[str] = set()
        self._pending_subs: Dict[int, Set[str]] = {i: set() for i in range(self._shard_count)}
        self._bg_tasks: Set[asyncio.Task] = set()
        self._shard_tasks: Dict[int, asyncio.Task] = {}
        self.log = get_logger('HyperFeed')

    def subscribe(self, tid: str) -> None:
        if tid not in self._token_set:
            self._token_set.add(tid)
            self._tokens.append(tid)
            self._books.setdefault(tid, OrderBook(token_id=tid))

    def book_ready(self, tid: str) -> bool:
        """True only after a clean snapshot and not crossed (LatArb must not trade on reconnect ghost books)."""
        if not tid or tid not in self._books:
            return False
        if tid not in self._snapshot_received:
            return False
        bk = self._books[tid]
        if bk is None or bk.is_crossed:
            return False
        return True

    def mark_shard_not_ready(self, tokens: List[str]) -> None:
        for tid in tokens:
            self._snapshot_received.discard(tid)

    async def subscribe_live(self, tids: List[str]) -> None:
        new = [t for t in tids if t not in self._token_set]
        if not new:
            return
        for tid in new:
            self.subscribe(tid)
        by_shard: Dict[int, List[str]] = {}
        for tid in new:
            shard_id = self._deterministic_shard(tid)
            self._pending_subs.setdefault(shard_id, set()).add(tid)
            by_shard.setdefault(shard_id, []).append(tid)
        sent = 0
        for shard_id, stids in by_shard.items():
            ws = self._ws_shards.get(shard_id)
            if ws is None:
                continue
            for i in range(0, len(stids), 10):
                batch = stids[i:i + 10]
                try:
                    # Parity with full-shard subscribe: custom_feature_enabled
                    # enables market_resolved push on live-added markets.
                    await ws.send(_json_dumps({'assets_ids': batch, 'operation': 'subscribe', 'custom_feature_enabled': True}))
                    for tid in batch:
                        self._pending_subs[shard_id].discard(tid)
                    sent += len(batch)
                    await asyncio.sleep(0.03)
                except Exception as e:
                    self.log.debug('live-sub send failed (shard %d): %s', shard_id, e)
        self.log.info('Live-subscribed %d tokens (queued %d for reconnect)', sent, len(new) - sent)

    def book(self, tid: str) -> Optional[OrderBook]:
        return self._books.get(tid)

    def last_trade(self, tid: str) -> Optional[float]:
        if time.monotonic() - self._trade_ts.get(tid, 0) > self.TRADE_TTL:
            return None
        return self._trade_ewma.get(tid)

    @property
    def last_msg_age_s(self) -> float:
        ages = self.shard_ages()
        if not ages:
            return float('inf')
        return max(ages.values())

    def shard_ages(self) -> Dict[int, float]:
        now = time.monotonic()
        shard_map = self._shard_tokens()
        return {sid: now - self._last_msgs.get(sid, 0.0) for sid, toks in shard_map.items() if toks}

    def on_update(self, cb: Callable) -> None:
        self._cbs.append(cb)

    def on_resolved(self, cb: Callable) -> None:
        self._resolved_cb = cb

    def _deterministic_shard(self, tid: str) -> int:
        return zlib.crc32(tid.encode()) % self._shard_count

    def _shard_tokens(self) -> Dict[int, List[str]]:
        shards: Dict[int, List[str]] = {i: [] for i in range(self._shard_count)}
        for tid in self._tokens:
            shards[self._deterministic_shard(tid)].append(tid)
        return shards

    async def run(self) -> None:
        self._running = True
        shard_map = self._shard_tokens()
        tasks = []
        for shard_id, tokens in shard_map.items():
            if tokens:
                t = asyncio.create_task(self._run_shard(shard_id, tokens), name=f'shard_{shard_id}')
                self._shard_tasks[shard_id] = t
                tasks.append(t)
        if tasks:
            self.log.info('Started %d shards (%d tokens total)', len(tasks), len(self._tokens))
            try:
                await asyncio.gather(*tasks)
            except asyncio.CancelledError:
                pass

    async def _run_shard(self, shard_id: int, tokens: List[str]) -> None:
        backoff = 1.0
        while self._running:
            live_tokens = self._shard_tokens().get(shard_id, tokens)
            pending = self._pending_subs.get(shard_id, set())
            if pending:
                merged = list({*live_tokens, *pending})
                live_tokens = merged
            for tid in live_tokens:
                self._snapshot_received.discard(tid)
            try:
                async with websockets.connect(self.WS_URL, ping_interval=10, ping_timeout=5, max_size=16 * 1024 * 1024, compression=None) as ws:
                    self._ws_shards[shard_id] = ws
                    backoff = 1.0
                    for i in range(0, len(live_tokens), 10):
                        await ws.send(_json_dumps({'auth': {}, 'type': 'Market', 'markets': [], 'assets_ids': live_tokens[i:i + 10], 'custom_feature_enabled': True}))
                        await asyncio.sleep(0.03)
                    self._pending_subs[shard_id] = set()
                    self._last_msgs[shard_id] = time.monotonic()
                    self.log.info('Shard %d: subscribed %d tokens', shard_id, len(live_tokens))
                    async for msg in ws:
                        if not self._running:
                            break
                        self._last_msgs[shard_id] = time.monotonic()
                        await self._handle(msg)
            except asyncio.CancelledError:
                live_tokens = self._shard_tokens().get(shard_id, tokens)
                self.mark_shard_not_ready(live_tokens)
                break
            except Exception as e:
                live_tokens = self._shard_tokens().get(shard_id, tokens)
                self.mark_shard_not_ready(live_tokens)
                self._ws_shards.pop(shard_id, None)
                if self._running:
                    self.log.warning('Shard %d WS error: %s (retry %.0fs) â€” books not ready until resnapshot', shard_id, e, backoff)
                    await asyncio.sleep(backoff * 0.5 + random.uniform(0.0, backoff * 0.5))
                    backoff = min(backoff * 2, 30)
        live_tokens = self._shard_tokens().get(shard_id, tokens)
        self.mark_shard_not_ready(live_tokens)
        self._ws_shards.pop(shard_id, None)

    async def restart_shard(self, shard_id: int) -> None:
        shard_map = self._shard_tokens()
        tokens = shard_map.get(shard_id, [])
        if tokens:
            self.log.info('Restarting shard %d (%d tokens)', shard_id, len(tokens))
            old_task = self._shard_tasks.pop(shard_id, None)
            if old_task and (not old_task.done()):
                old_task.cancel()
                try:
                    await old_task
                except (asyncio.CancelledError, Exception):
                    pass
            old_ws = self._ws_shards.pop(shard_id, None)
            if old_ws:
                try:
                    await old_ws.close()
                except Exception:
                    pass
            t = asyncio.create_task(self._run_shard(shard_id, tokens), name=f'shard_{shard_id}_restart')
            self._shard_tasks[shard_id] = t
            self._bg_tasks.add(t)
            t.add_done_callback(self._bg_tasks.discard)

    async def _handle(self, raw: str) -> None:
        try:
            msgs = _json_loads(raw)
        except Exception as e:
            self.log.debug('WS parse error: %s', e)
            return
        if not isinstance(msgs, list):
            msgs = [msgs]
        for m in msgs:
            try:
                et = m.get('event_type', '')
                tid = m.get('asset_id', '')
                if et == 'market_resolved':
                    cb = self._resolved_cb
                    if cb is not None:
                        try:
                            t = asyncio.create_task(cb(m))
                            self._bg_tasks.add(t)
                            t.add_done_callback(self._bg_tasks.discard)
                        except Exception as rcb_err:
                            self.log.warning('resolved cb error: %s', rcb_err)
                    continue
                if et == 'price_change':
                    delta_ts = time.monotonic()
                    msg_ex_ts = _ws_exchange_ts_ms(m)
                    _delta_touched: Set[str] = set()  # L1 FIX
                    for c in m.get('price_changes', m.get('changes', [])):
                        c_tid = c.get('asset_id', tid)
                        if c_tid not in self._books or c_tid not in self._snapshot_received:
                            continue
                        bk = self._books[c_tid]
                        s = c.get('side', '').upper()
                        if s not in ('BUY', 'SELL', 'BID', 'ASK'):
                            continue
                        try:
                            p = float(c['price'])
                            sz = float(c['size'])
                        except (KeyError, ValueError, TypeError):
                            continue
                        if not math.isfinite(p) or not math.isfinite(sz) or p <= 0 or (sz < 0):
                            continue
                        c_ex = _ws_exchange_ts_ms(c) if isinstance(c, dict) else None
                        ex_ts = c_ex if c_ex is not None else msg_ex_ts
                        # Reject out-of-order venue stamps so delayed msgs cannot look "fresh".
                        if not bk.touch(delta_ts, ex_ts, allow_regression=False):
                            self.log.debug('out-of-order delta dropped %s ex_ts=%s prev=%s', c_tid[:10], ex_ts, bk.exchange_ts_ms)
                            continue
                        bk.apply_delta(p, sz, is_bid=s in ('BUY', 'BID'))
                        # Crossed book after delta = phantom depth; force
                        # re-snapshot before any further delta trading.
                        if bk.is_crossed:
                            self._snapshot_received.discard(c_tid)
                            bk.exchange_ts_ms = None
                            _delta_touched.discard(c_tid)
                            self.log.debug('crossed book %s after delta â€” awaiting snapshot', c_tid[:10])
                        else:
                            _delta_touched.add(c_tid)
                    # L1 FIX: fan callbacks out on delta-updated books (once per
                    # token per message) so Polymarket-side moves trigger eval in
                    # event-driven mode, not only 'book' snapshots / Binance ticks.
                    for c_tid in _delta_touched:
                        d_bk = self._books.get(c_tid)
                        if d_bk is None:
                            continue
                        for cb in self._cbs:
                            try:
                                t = asyncio.create_task(cb(c_tid, d_bk))
                                self._bg_tasks.add(t)
                                t.add_done_callback(self._bg_tasks.discard)
                            except Exception as cb_err:
                                self.log.warning('book cb error: %s', cb_err)
                    continue
                if tid not in self._books:
                    continue
                bk = self._books[tid]
                if et == 'book':

                    def _levels(rows):
                        out = []
                        for x in rows or []:
                            try:
                                p = float(x['price'])
                                sz = float(x['size'])
                            except (KeyError, ValueError, TypeError):
                                continue
                            if math.isfinite(p) and math.isfinite(sz) and (p > 0) and (sz > 0):
                                out.append((p, sz))
                        return out
                    bids = _levels(m.get('bids', []))
                    asks = _levels(m.get('asks', []))
                    bk.replace_snapshot(bids, asks)
                    # Snapshots always win (allow_regression): resync venue clock after reconnect.
                    bk.touch(time.monotonic(), _ws_exchange_ts_ms(m), allow_regression=True)
                    if bk.is_crossed:
                        self._snapshot_received.discard(tid)
                        bk.exchange_ts_ms = None
                        self.log.debug('crossed snapshot %s â€” not trading until clean book', tid[:10])
                    else:
                        self._snapshot_received.add(tid)
                elif et == 'last_trade_price':
                    try:
                        price = float(m['price'])
                    except (KeyError, ValueError, TypeError):
                        continue
                    try:
                        size = float(m.get('size', 0.0))
                    except (TypeError, ValueError):
                        size = 0.0
                    if math.isfinite(price) and 0 < price < 1:
                        prev = self._trade_ewma.get(tid)
                        self._trade_ewma[tid] = self.TRADE_ALPHA * price + (1 - self.TRADE_ALPHA) * prev if prev is not None else price
                        self._trade_ts[tid] = time.monotonic()
                        if self._whale_threshold_usdc > 0.0 and math.isfinite(size) and (size > 0.0) and (size * price >= self._whale_threshold_usdc):
                            self._last_large_trade_ts[tid] = time.monotonic()
                            self.log.info('WHALE %s | %.0f @ %.3f = $%.0f (>= $%.0f)', tid[:10], size, price, size * price, self._whale_threshold_usdc)
                for cb in self._cbs:
                    try:
                        t = asyncio.create_task(cb(tid, bk))
                        self._bg_tasks.add(t)
                        t.add_done_callback(self._bg_tasks.discard)
                    except Exception as cb_err:
                        self.log.warning('book cb error: %s', cb_err)
            except Exception as inner:
                self.log.debug('WS msg dispatch error: %s', inner)

    async def unsubscribe(self, tids: List[str]) -> None:
        shard_groups: Dict[int, List[str]] = {}
        for tid in tids:
            sid = self._deterministic_shard(tid)
            shard_groups.setdefault(sid, []).append(tid)
            self._token_set.discard(tid)
            self._books.pop(tid, None)
            self._trade_ewma.pop(tid, None)
            self._trade_ts.pop(tid, None)
            self._snapshot_received.discard(tid)
        self._tokens = [t for t in self._tokens if t in self._token_set]
        for sid, stids in shard_groups.items():
            ws = self._ws_shards.get(sid)
            if ws:
                try:
                    await ws.send(_json_dumps({'assets_ids': stids, 'operation': 'unsubscribe'}))
                except Exception:
                    pass
        self.log.debug('Unsubscribed %d tokens (%d remain)', len(tids), len(self._tokens))

    async def stop(self) -> None:
        self._running = False
        tasks = [t for t in self._shard_tasks.values() if not t.done()]
        for t in tasks:
            t.cancel()
        if tasks:
            await asyncio.gather(*tasks, return_exceptions=True)
        for ws in list(self._ws_shards.values()):
            try:
                await ws.close()
            except Exception:
                pass
        self._ws_shards.clear()
        self._shard_tasks.clear()

class UserFeed:
    WS_URL = 'wss://ws-subscriptions-clob.polymarket.com/ws/user'

    def __init__(self, client: PolyClient, om: OrderManager) -> None:
        self._client = client
        self._om = om
        self._lookup: Dict[str, Market] = {}
        self._mids: List[str] = []
        self._fill_cbs: List[Callable] = []
        self._running = False
        self.connected = False
        self._ws: Optional[Any] = None
        self._subscribed_mids: Set[str] = set()
        self._last_msg_ts: float = 0.0
        self._ws_fill_seq: int = 0
        self._bg_tasks: Set[asyncio.Task] = set()  # N2 FIX: retain fire-and-forget tasks
        self.log = get_logger('UserFeed')

    def set_markets(self, t2m: Dict[str, Market]) -> None:
        self._lookup = t2m
        self._mids = list({m.condition_id or m.market_id for m in t2m.values()})
        if self.connected and self._ws is not None:
            new_mids = [mid for mid in self._mids if mid and mid not in self._subscribed_mids]
            if new_mids:
                try:
                    # N2 FIX: retain the task so it cannot be garbage-collected
                    # mid-flight and a failure is observed via its done callback.
                    t = asyncio.get_running_loop().create_task(self._incremental_subscribe(new_mids))
                    self._bg_tasks.add(t)
                    t.add_done_callback(self._bg_tasks.discard)
                except RuntimeError:
                    pass

    async def _incremental_subscribe(self, mids: List[str]) -> None:
        ws = self._ws
        if ws is None or not self.connected:
            return
        try:
            await ws.send(_json_dumps({'markets': mids, 'operation': 'subscribe'}))
            self._subscribed_mids.update(mids)
            self.log.info('incremental subscribe: +%d markets', len(mids))
        except Exception as e:
            self.log.warning('incremental subscribe failed: %s', e)

    def on_fill(self, cb: Callable) -> None:
        self._fill_cbs.append(cb)

    @property
    def last_msg_age_s(self) -> float:
        if self._last_msg_ts <= 0:
            return float('inf')
        return time.monotonic() - self._last_msg_ts

    async def run(self) -> None:
        if not self._client.api_key:
            self.log.warning('No API key â€” user feed disabled')
            return
        self._running = True
        backoff = 1.0
        while self._running:
            try:
                async with websockets.connect(self.WS_URL, ping_interval=30, ping_timeout=15, close_timeout=5, max_size=5 * 1024 * 1024, compression=None) as ws:
                    sub = {'type': 'User', 'markets': self._mids, 'assets_ids': [], 'auth': {'apiKey': self._client.api_key, 'secret': self._client.api_secret, 'passphrase': self._client.api_passphrase}}
                    await ws.send(_json_dumps(sub))
                    try:
                        await asyncio.wait_for(ws.recv(), timeout=5.0)
                    except asyncio.TimeoutError:
                        pass
                    self.log.info('Connected (%d markets)', len(self._mids))
                    self.connected = True
                    self._ws = ws
                    self._subscribed_mids = {m for m in self._mids if m}
                    backoff = 1.0
                    async for msg in ws:
                        if not self._running:
                            break
                        try:
                            msgs = _json_loads(msg)
                            self._last_msg_ts = time.monotonic()
                            if not isinstance(msgs, list):
                                msgs = [msgs]
                            for m in msgs:
                                if m.get('event_type', '') not in ('trade', 'order_fill', 'match'):
                                    continue
                                tid = m.get('asset_id') or m.get('token_id', '')
                                mkt = self._lookup.get(tid)
                                if not mkt:
                                    continue
                                p = float(m.get('price', 0))
                                sz = float(m.get('size') or m.get('quantity', 0))
                                sd = str(m.get('side', '')).upper()
                                if not p or not sz or sd not in ('BUY', 'SELL'):
                                    continue
                                _real_id = m.get('trade_id') or m.get('id') or m.get('match_id')
                                if not _real_id:
                                    self.log.warning('Identifier-less WS fill deferred to REST reconciliation for token %s', str(tid)[:12])
                                    continue
                                ws_trade_id = str(_real_id)
                                if self._om.has_seen_trade(ws_trade_id):
                                    continue
                                order_ids = self._om._extract_trade_order_ids(m)
                                try:
                                    for cb in self._fill_cbs:
                                        await cb(mkt, tid, sd, sz, p, ws_trade_id, order_ids, False)
                                except Exception as cb_err:
                                    self._om.latch_fill_failure(f'WS fill {ws_trade_id} apply failed: {cb_err}')
                                    self.log.exception('Fill callback error; event left unacknowledged: %s', cb_err)
                                    continue
                                self._om.mark_trade_seen(ws_trade_id)
                                self.log.info("FILL %s %s %.2f@%.4f id=%s  '%s'", sd, tid[:12], sz, p, ws_trade_id[:16], mkt.question[:30])
                        except Exception as ex:
                            self.log.debug('Parse error: %s', ex)
            except asyncio.CancelledError:
                self.connected = False
                self._ws = None
                self._subscribed_mids.clear()
                break
            except Exception as e:
                self.connected = False
                self._ws = None
                self._subscribed_mids.clear()
                if self._running:
                    self.log.warning('WS error: %s (retry in %.0fs)', e, backoff)
                    await asyncio.sleep(backoff * 0.5 + random.uniform(0.0, backoff * 0.5))
                    backoff = min(backoff * 2, 30)

    async def stop(self) -> None:
        self._running = False
        self.connected = False
        self._ws = None
        self._subscribed_mids.clear()
COIN_KW: Dict[str, Set[str]] = {'BTC': {'btc', 'bitcoin'}, 'ETH': {'eth', 'ethereum'}, 'SOL': {'sol', 'solana'}, 'XRP': {'xrp', 'ripple'}, 'BNB': {'bnb', 'binance'}, 'DOGE': {'doge', 'dogecoin'}, 'MATIC': {'matic', 'polygon'}, 'ADA': {'ada', 'cardano'}}

def detect_coin(q: str) -> Optional[str]:
    words = set(re.findall('[a-zA-Z]+', q.lower()))
    matched: List[str] = []
    for c, kw in COIN_KW.items():
        if kw & words:
            matched.append(c)
    if len(matched) == 1:
        return matched[0]
    return None

def _parse_end_time(raw: dict) -> Optional[float]:
    for k in ('endDate', 'end_date', 'endDateIso', 'end_date_iso'):
        v = raw.get(k)
        if v:
            try:
                if isinstance(v, (int, float)):
                    return float(v)
                s = str(v).replace('Z', '+00:00')
                dt = datetime.fromisoformat(s)
                if dt.tzinfo is None:
                    dt = dt.replace(tzinfo=timezone.utc)
                return dt.timestamp()
            except Exception:
                pass
    return None

def _jlist(v: Any) -> list:
    if isinstance(v, list):
        return v
    if isinstance(v, str):
        try:
            r = json.loads(v)
            if isinstance(r, list):
                return r
        except Exception:
            pass
    return []

async def discover_5min_markets(cfg: Config, session: aiohttp.ClientSession) -> List[Market]:
    dlog = get_logger('5MinDiscovery', cfg.log_level)
    now = time.time()
    found: List[Market] = []
    for coin in cfg.coins:
        coin_lower = coin.lower()
        for tf_label, tf_secs in [('5m', 300), ('15m', 900)]:
            epoch = int(now - now % tf_secs)
            for offset in [0, tf_secs]:
                slug = f'{coin_lower}-updown-{tf_label}-{epoch + offset}'
                try:
                    async with session.get(f'{cfg.gamma_url}/markets', params={'slug': slug, 'closed': 'false'}, timeout=aiohttp.ClientTimeout(total=6)) as r:
                        if not r.ok:
                            continue
                        data = await r.json(content_type=None)
                        items = data if isinstance(data, list) else [data] if isinstance(data, dict) and data.get('id') else []
                        for raw in items:
                            mkt = _parse_5min_market(raw, cfg, now, tf_secs)
                            if mkt:
                                found.append(mkt)
                except Exception:
                    pass
    if len(found) < 2:
        for kw_params in [{'closed': 'false', 'limit': '100', 'offset': '0'}]:
            try:
                async with session.get(f'{cfg.gamma_url}/markets', params=kw_params, timeout=aiohttp.ClientTimeout(total=12)) as r:
                    if not r.ok:
                        continue
                    data = await r.json(content_type=None)
                    items = data if isinstance(data, list) else data.get('markets', [])
                    for raw in items:
                        q = raw.get('question') or raw.get('title') or ''
                        slug = raw.get('slug') or ''
                        has_5m = bool(re.search('5[\\s-]*min', q, re.IGNORECASE) or '5m' in slug)
                        has_15m = bool(re.search('15[\\s-]*min', q, re.IGNORECASE) or '15m' in slug)
                        is_updown = 'up or down' in q.lower()
                        if not ((has_5m or has_15m) and is_updown):
                            continue
                        coin = detect_coin(q)
                        if not coin or coin not in cfg.coins:
                            continue
                        tf_secs = 900 if has_15m else 300
                        mkt = _parse_5min_market(raw, cfg, now, tf_secs)
                        if mkt:
                            found.append(mkt)
            except Exception:
                pass
    seen: Set[str] = set()
    unique: List[Market] = []
    for m in found:
        if m.market_id not in seen:
            seen.add(m.market_id)
            unique.append(m)
    unique.sort(key=lambda m: m.liquidity, reverse=True)
    dlog.info('Found %d 5-min markets for %s', len(unique), cfg.coins)
    return unique

def _parse_5min_market(raw: dict, cfg: Config, now: float, tf_secs: int=300) -> Optional[Market]:
    try:
        tids = _jlist(raw.get('clobTokenIds'))
        outs = _jlist(raw.get('outcomes'))
        if len(tids) < 2:
            return None
        yes_id = no_id = None
        for i, o in enumerate(outs[:len(tids)]):
            ol = str(o).strip().lower()
            if ol in ('yes', 'up', 'higher', 'more', 'above', 'over'):
                yes_id = str(tids[i])
            elif ol in ('no', 'down', 'lower', 'less', 'below', 'under'):
                no_id = str(tids[i])
        yes_id = yes_id or str(tids[0])
        no_id = no_id or str(tids[1])
        if not yes_id or not no_id or yes_id == no_id:
            return None
        mid = str(raw.get('id') or raw.get('conditionId') or '')
        cond_id = str(raw.get('conditionId') or raw.get('condition_id') or '')
        q = raw.get('question') or raw.get('title') or ''
        if not mid or not q:
            return None
        if raw.get('closed', False):
            return None
        if not raw.get('acceptingOrders', True):
            return None
        et = _parse_end_time(raw)
        if et and et < now:
            return None
        coin = detect_coin(q)
        if coin and coin not in cfg.coins:
            return None
        liq = float(raw.get('liquidityClob') or raw.get('liquidityNum') or raw.get('liquidity') or 0)
        fees_en = bool(raw.get('feesEnabled') if raw.get('feesEnabled') is not None else raw.get('fees_enabled') or False)
        fee_rate: Optional[float] = None
        for _fk in ('feeRate', 'takerBaseFee', 'taker_base_fee', 'makerBaseFee'):
            if raw.get(_fk) is None:
                continue
            try:
                _rv = float(raw[_fk])
            except (TypeError, ValueError):
                continue
            if _rv <= 0:
                fee_rate = 0.0
            elif _rv <= 1.0:
                fee_rate = _rv
            else:
                # integer bps (e.g. 700 â†’ 0.07) or percent-like
                fee_rate = _rv / 10000.0 if _rv >= 10 else _rv / 100.0
            fees_en = fees_en or fee_rate > 0
            break
        return Market(market_id=mid, question=q, yes_token=yes_id, no_token=no_id, condition_id=cond_id, end_time=et, coin=coin, tf_secs=tf_secs, liquidity=liq, volatility=abs(float(raw.get('oneDayPriceChange') or 0)), neg_risk=bool(raw.get('negRisk') or raw.get('neg_risk') or False), fees_enabled=fees_en, fee_rate=fee_rate)
    except Exception:
        return None

def _fee_per_share(rate: float, px: float, exponent: float=1.0) -> float:
    """Polymarket V2 taker fee: feeRate * (p * (1-p)) ** exponent per share."""
    if rate is None or rate <= 0:
        return 0.0
    p = max(1e-06, min(1.0 - 1e-06, float(px)))
    base = p * (1.0 - p)
    exp = float(exponent) if exponent is not None and math.isfinite(float(exponent)) else 1.0
    if exp <= 0:
        exp = 1.0
    try:
        return max(0.0, float(rate)) * (base ** exp)
    except Exception:
        return max(0.0, float(rate)) * base

def _market_fee_rate(mkt: Optional['Market'], cfg: 'Config') -> float:
    """Per-market feeRate coefficient; falls back to CATEGORY_FEE_RATE when unknown."""
    if mkt is not None and getattr(mkt, 'fee_rate', None) is not None:
        if not getattr(mkt, 'fees_enabled', True) and float(mkt.fee_rate or 0.0) <= 0.0:
            return 0.0
        return max(0.0, float(mkt.fee_rate))
    return max(0.0, float(getattr(cfg, 'category_fee_rate', 0.0) or 0.0))

def _market_fee_exponent(mkt: Optional['Market']) -> float:
    if mkt is None:
        return 1.0
    try:
        e = float(getattr(mkt, 'fee_exponent', 1.0) or 1.0)
        return e if e > 0 and math.isfinite(e) else 1.0
    except Exception:
        return 1.0

def _market_fee_per_share(mkt: Optional['Market'], cfg: 'Config', px: float) -> float:
    return _fee_per_share(_market_fee_rate(mkt, cfg), px, _market_fee_exponent(mkt))

SIGMA_PER_SEC_MAX = 0.05

class PriceTracker:
    WINDOW = 2700
    _EWMA_ALPHA = 0.03

    def __init__(self, feed: Any, prob_shrink: float=1.0, min_order_size_usdc: float=0.0, momentum_weight: float=0.0):
        # feed: ChainlinkFeed (settlement oracle) preferred; BinanceFeed acceptable as fallback.
        self.feed = feed
        self.prob_shrink = prob_shrink
        self._per_coin_shrink: Dict[str, float] = {}
        self._min_order_size_usdc: float = max(0.0, min_order_size_usdc)
        self._momentum_weight: float = max(0.0, momentum_weight)
        self._history: Dict[str, Deque[Tuple[float, float]]] = {}
        self._vwap_num: Dict[str, float] = {}
        self._vwap_den: Dict[str, float] = {}
        self._ewma_var: Dict[str, float] = {}
        self._ewma_mean: Dict[str, float] = {}
        # Lead feed (Binance) EWMA â€” higher tick rate; used for LatArb sigma only.
        self._lead_ewma_var: Dict[str, float] = {}
        self._lead_ewma_mean: Dict[str, float] = {}
        self._lead_last: Dict[str, Tuple[float, float]] = {}
        self._ts_index: Dict[str, List[float]] = {}
        self._px_by_ts: Dict[str, List[float]] = {}
        self.log = get_logger('PriceTracker')
        feed.on_update(self._on_price)

    def _update_ewma(self, store_var: Dict[str, float], store_mean: Dict[str, float], coin: str, ret: float) -> None:
        alpha = self._EWMA_ALPHA
        old_mean = store_mean.get(coin, 0.0)
        new_mean = alpha * ret + (1.0 - alpha) * old_mean
        old_var = store_var.get(coin, ret * ret)
        new_var = alpha * (ret - old_mean) ** 2 + (1.0 - alpha) * old_var
        store_mean[coin] = new_mean
        store_var[coin] = new_var

    async def ingest_lead_tick(self, coin: str, price: float) -> None:
        """High-frequency lead (Binance) tick â†’ vol EWMA only. Does not rewrite settlement history."""
        if not isinstance(price, (int, float)) or not math.isfinite(price) or price <= 0:
            return
        now = time.time()
        prev = self._lead_last.get(coin)
        self._lead_last[coin] = (now, price)
        if not prev:
            return
        prev_ts, prev_px = prev
        dt = now - prev_ts
        if dt < 0.05 or dt > 30.0 or prev_px <= 0:
            return
        ret_raw = math.log(price / prev_px)
        if not math.isfinite(ret_raw):
            return
        ret = ret_raw / math.sqrt(max(dt, 0.001))
        if math.isfinite(ret):
            self._update_ewma(self._lead_ewma_var, self._lead_ewma_mean, coin, ret)

    async def _on_price(self, coin: str, price: float) -> None:
        if not isinstance(price, (int, float)) or not math.isfinite(price) or price <= 0:
            return
        now = time.time()
        if coin not in self._history:
            self._history[coin] = deque()
            self._vwap_num[coin] = 0.0
            self._vwap_den[coin] = 0.0
        dq = self._history[coin]
        if not dq or now - dq[-1][0] >= 1.0:
            prev_1hz = dq[-1][1] if dq else None
            prev_ts = dq[-1][0] if dq else None
            dq.append((now, price))
            new_bucket = True
            ts_list = self._ts_index.setdefault(coin, [])
            px_list = self._px_by_ts.setdefault(coin, [])
            ts_list.append(now)
            px_list.append(price)
        else:
            dq[-1] = (dq[-1][0], price)
            prev_1hz = None
            prev_ts = None
            new_bucket = False
            px_list = self._px_by_ts.get(coin)
            if px_list:
                px_list[-1] = price
        self._vwap_num[coin] = self._vwap_num.get(coin, 0.0) * 0.999 + price
        self._vwap_den[coin] = self._vwap_den.get(coin, 0.0) * 0.999 + 1.0
        if new_bucket and prev_1hz and (prev_1hz > 0) and (prev_ts is not None):
            dt = now - prev_ts
            ret_raw = math.log(price / prev_1hz)
            if dt > 30.0 or not math.isfinite(ret_raw):
                ret = None
            else:
                ret = ret_raw / math.sqrt(max(dt, 0.001))
            if ret is not None and math.isfinite(ret):
                self._update_ewma(self._ewma_var, self._ewma_mean, coin, ret)
        cutoff = now - self.WINDOW
        while dq and dq[0][0] < cutoff:
            dq.popleft()
        ts_list = self._ts_index.get(coin)
        px_list = self._px_by_ts.get(coin)
        if ts_list:
            cutoff_idx = bisect.bisect_left(ts_list, cutoff)
            if cutoff_idx > 0:
                del ts_list[:cutoff_idx]
                if px_list is not None:
                    del px_list[:cutoff_idx]

    def get_price_at(self, coin: str, target_ts: float, max_gap_s: float=10.0) -> Optional[float]:
        ts_list = self._ts_index.get(coin)
        px_list = self._px_by_ts.get(coin)
        if not ts_list or not px_list:
            return None
        idx = bisect.bisect_left(ts_list, target_ts)
        best_idx, best_gap = (-1, float('inf'))
        for i in (idx - 1, idx):
            if 0 <= i < len(ts_list):
                gap = abs(ts_list[i] - target_ts)
                if gap < best_gap:
                    best_gap, best_idx = (gap, i)
        if best_idx < 0 or best_gap > max_gap_s:
            return None
        return px_list[best_idx]

    def get_price_at_or_before(self, coin: str, target_ts: float, max_lag_s: float=10.0) -> Optional[float]:
        ts_list = self._ts_index.get(coin)
        px_list = self._px_by_ts.get(coin)
        if not ts_list or not px_list:
            return None
        idx = bisect.bisect_right(ts_list, target_ts) - 1
        if idx < 0:
            return None
        lag = target_ts - ts_list[idx]
        if lag < 0 or lag > max_lag_s:
            return None
        return px_list[idx]

    def _log_returns(self, coin: str, n: Optional[int]=None) -> List[float]:
        dq = self._history.get(coin)
        if not dq or len(dq) < 10:
            return []
        if n is None or n >= len(dq) - 1:
            prices = [p for _, p in dq]
        else:
            tail = list(itertools.islice(reversed(dq), n + 1))
            tail.reverse()
            prices = [p for _, p in tail]
        return [math.log(prices[i] / prices[i - 1]) for i in range(1, len(prices)) if prices[i - 1] > 0]

    def volatility(self, coin: str) -> float:
        # Prefer lead-feed (Binance) EWMA when present â€” Chainlink RTDS is too smooth
        # and was pinning sigma at GBM_SIGMA_FLOOR forever (breaks z / model_prob).
        for store in (self._lead_ewma_var, self._ewma_var):
            ewma_var = store.get(coin)
            if ewma_var is not None and ewma_var > 0:
                return min(max(math.sqrt(ewma_var), 1e-08), SIGMA_PER_SEC_MAX)
        rets = self._log_returns(coin)
        if len(rets) < 10:
            return 0.001
        mean = sum(rets) / len(rets)
        var = sum(((r - mean) ** 2 for r in rets)) / len(rets)
        return min(max(math.sqrt(var), 1e-08), SIGMA_PER_SEC_MAX)

    def velocity(self, coin: str, window_s: int=30) -> float:
        dq = self._history.get(coin)
        if not dq or len(dq) < 2:
            return 0.0
        now = time.time()
        cutoff = now - window_s
        window_pts = [(ts, p) for ts, p in dq if ts >= cutoff]
        if len(window_pts) < 2:
            return 0.0
        if window_pts[-1][0] - window_pts[0][0] < 0.5 * window_s:
            return 0.0
        old_price = window_pts[0][1]
        if old_price <= 0:
            return 0.0
        cur_price = dq[-1][1]
        if cur_price <= 0:
            return 0.0
        return math.log(cur_price / old_price)

    def roc(self, coin: str, lookback_s: int=60) -> float:
        dq = self._history.get(coin)
        if not dq or len(dq) < 5:
            return 0.0
        now = time.time()
        cutoff = now - lookback_s
        old_pts = [(t, p) for t, p in dq if t >= cutoff]
        if len(old_pts) < 2:
            return 0.0
        return (old_pts[-1][1] - old_pts[0][1]) / old_pts[0][1]

    def is_choppy(self, coin: str, tf_secs: int=300) -> bool:
        roc_30 = abs(self.roc(coin, 30))
        roc_60 = abs(self.roc(coin, 60))
        sigma = self.volatility(coin)
        return roc_30 < 0.0002 and roc_60 < 0.0003 and (sigma > 0.0003)

    def prob_up(self, coin: str, current_price: float, open_price: float, tau_s: float, yes_book: Optional[OrderBook]=None, yes_trade_ewma: Optional[float]=None, btc_displacement: Optional[float]=None) -> float:
        if open_price <= 0 or current_price <= 0 or tau_s <= 0 or (not math.isfinite(current_price)) or (not math.isfinite(open_price)):
            return 0.5
        sigma_per_sec = max(self.volatility(coin), GBM_SIGMA_FLOOR_PER_SEC)
        if not math.isfinite(sigma_per_sec) or sigma_per_sec <= 0:
            return 0.5
        sigma_horizon = sigma_per_sec * math.sqrt(max(tau_s, 0.0001))
        if not math.isfinite(sigma_horizon) or sigma_horizon <= 0:
            return 0.5
        log_disp = math.log(current_price / open_price)
        if not math.isfinite(log_disp):
            return 0.5
        if sigma_horizon < 1e-06:
            return 0.98 if log_disp > 0 else 0.02
        ito_drag = 0.5 * sigma_per_sec * sigma_per_sec * tau_s
        mu_tau = 0.0
        mw = self._momentum_weight
        if mw > 0.0:
            raw_mu = self._ewma_mean.get(coin, 0.0)
            if math.isfinite(raw_mu):
                mu_sec = max(-sigma_per_sec, min(sigma_per_sec, raw_mu))
                mu_tau = mu_sec * tau_s
                if sigma_horizon > 0:
                    mu_tau = max(-sigma_horizon, min(sigma_horizon, mu_tau))
        z = (log_disp + mw * mu_tau - ito_drag) / sigma_horizon
        base = 0.5 * (1.0 + math.erf(z / math.sqrt(2.0)))
        tilt = 0.0
        if yes_book is not None:
            ofi_thin = yes_book.top_depth_usdc < 2.0 * (self._min_order_size_usdc or 0.0)
            if ofi_thin:
                ofi = 0.0
            else:
                top_bids = heapq.nlargest(3, yes_book._bids_int.keys()) if yes_book._bids_int else []
                top_asks = heapq.nsmallest(3, yes_book._asks_int.keys()) if yes_book._asks_int else []
                top_bid_vol = sum((yes_book._bids_int.get(k, 0) for k in top_bids))
                top_ask_vol = sum((yes_book._asks_int.get(k, 0) for k in top_asks))
                total_top = top_bid_vol + top_ask_vol
                ofi = max(-0.5, min(0.5, top_bid_vol / total_top - 0.5 if total_top > 0 else 0.0))
            tilt += 0.08 * ofi
            if yes_trade_ewma is not None:
                book_mid = yes_book.mid
                if book_mid is not None and book_mid > 0:
                    drift = max(-1.0, min(1.0, (yes_trade_ewma - book_mid) / 0.02))
                    tilt += 0.02 * drift
        if btc_displacement is not None and coin != 'BTC':
            tilt += 0.03 * max(-1.0, min(1.0, btc_displacement / 0.003))
        p = base + tilt
        coin_shrink = max(0.0, min(1.0, self._per_coin_shrink.get(coin, self.prob_shrink)))
        p = 0.5 + (p - 0.5) * coin_shrink
        return max(0.02, min(0.98, p))

def _round_trip_cost(book: Optional[OrderBook], size_usdc: float) -> Tuple[float, float, bool]:
    if not book or size_usdc <= 0:
        return (float('inf'), 0.0, False)
    PS = OrderBook.PRICE_SCALE
    SS = OrderBook.SIZE_SCALE
    rem_scaled = int(round(size_usdc * PS * SS))
    cost_scaled: int = 0
    shares_int: int = 0
    for key in sorted(book._asks_int.keys()):
        if key <= 0:
            continue
        level_size_int = book._asks_int[key]
        level_notional = key * level_size_int
        if level_notional <= rem_scaled:
            cost_scaled += level_notional
            shares_int += level_size_int
            rem_scaled -= level_notional
        else:
            taken_int = rem_scaled // key
            if taken_int > 0:
                cost_scaled += taken_int * key
                shares_int += taken_int
            rem_scaled = 0
            break
        if rem_scaled <= 0:
            break
    if rem_scaled > 0 or shares_int <= 0:
        return (float('inf'), 0.0, False)
    entry_per_share = cost_scaled / shares_int / PS
    rem_shares = shares_int
    rev_scaled: int = 0
    shares_out_int: int = 0
    for key in sorted(book._bids_int.keys(), reverse=True):
        if key <= 0:
            continue
        level_size_int = book._bids_int[key]
        if level_size_int <= rem_shares:
            rev_scaled += key * level_size_int
            shares_out_int += level_size_int
            rem_shares -= level_size_int
        else:
            taken_int = rem_shares
            if taken_int > 0:
                rev_scaled += taken_int * key
                shares_out_int += taken_int
            rem_shares = 0
            break
        if rem_shares <= 0:
            break
    if rem_shares > 0 or shares_out_int <= 0:
        exit_per_share = rev_scaled / shares_out_int / PS if shares_out_int > 0 else 0.0
        return (entry_per_share, exit_per_share, False)
    exit_per_share = rev_scaled / shares_out_int / PS
    return (entry_per_share, exit_per_share, True)

def _entry_vwap_from_asks(book: Optional[OrderBook], size_usdc: float) -> Tuple[float, float, bool]:
    if not book or not book._asks_int or size_usdc <= 0:
        return (float('inf'), 0.0, False)
    PS = OrderBook.PRICE_SCALE
    SS = OrderBook.SIZE_SCALE
    rem_scaled = int(round(size_usdc * PS * SS))
    cost_scaled = 0
    shares_int = 0
    for key in sorted(book._asks_int.keys()):
        if key <= 0:
            continue
        level_size_int = book._asks_int[key]
        level_notional = key * level_size_int
        if level_notional <= rem_scaled:
            cost_scaled += level_notional
            shares_int += level_size_int
            rem_scaled -= level_notional
        else:
            taken_int = rem_scaled // key
            if taken_int > 0:
                cost_scaled += taken_int * key
                shares_int += taken_int
            rem_scaled = 0
            break
        if rem_scaled <= 0:
            break
    if rem_scaled > 0 or shares_int <= 0:
        return (float('inf'), 0.0, False)
    return (cost_scaled / shares_int / PS, shares_int / SS, True)

def _estimate_slippage(book: Optional[OrderBook], size_usdc: float) -> float:
    if not book or not book._asks_int or size_usdc <= 0:
        return 0.99
    best_ask = book.best_ask
    if best_ask is None:
        return 0.99
    entry_per_share, _, fillable = _entry_vwap_from_asks(book, size_usdc)
    if not fillable or entry_per_share == float('inf'):
        return 0.99
    return max(0.001, entry_per_share - best_ask)

def kelly_size(p_final: float, entry_price: float, entry_slip: float, exit_slip: float, *, kelly_fraction: float, bankroll: float, max_bankroll_fraction: float, min_order_size: float, max_order_size: float, cold_start: bool=False, negative_ev_skips: bool=True, full_kelly_cap: float=0.25, p_hold_to_expiry: float=0.6, taker_fee_bps: float=20.0, category_fee_rate: float=0.0) -> float:
    if not 0.0 < p_final < 1.0:
        return 0.0 if negative_ev_skips else min_order_size
    if category_fee_rate > 0:
        _pf = max(1e-06, min(1.0 - 1e-06, entry_price))
        fee_per_share = max(0.0, category_fee_rate) * _pf * (1.0 - _pf)
    else:
        fee_per_share = max(0.0, taker_fee_bps) * 0.0001 * max(0.0, entry_price)
    Cin = entry_price + max(0.0, entry_slip) + fee_per_share
    p_hold = max(0.0, min(1.0, p_hold_to_expiry))
    Cout_redeem = 1.0
    Cout_early = 1.0 - max(0.0, exit_slip)
    # N9 FIX: an early exit is a taker SELL and pays the fee at the exit price;
    # redemption at expiry does not.  Mirror the entry fee curve at the modeled
    # exit price so EV is not systematically overstated for early exits.
    _pe = max(1e-06, min(1.0 - 1e-06, Cout_early))
    if category_fee_rate > 0:
        exit_fee_per_share = max(0.0, category_fee_rate) * _pe * (1.0 - _pe)
    else:
        exit_fee_per_share = max(0.0, taker_fee_bps) * 0.0001 * _pe
    Cout_early = max(0.0, Cout_early - exit_fee_per_share)
    Cout = p_hold * Cout_redeem + (1.0 - p_hold) * Cout_early
    if not 0.0 < Cin < 1.0:
        return 0.0 if negative_ev_skips else min_order_size
    if Cout <= Cin:
        return 0.0 if negative_ev_skips else min_order_size
    p = max(1e-06, min(1.0 - 1e-06, p_final))
    q = 1.0 - p
    b = (Cout - Cin) / Cin
    ev = p * b - q
    if ev <= 0.0:
        return 0.0 if negative_ev_skips else min_order_size
    f = max(0.0, min(full_kelly_cap, ev / b))
    frac = kelly_fraction * (0.5 if cold_start else 1.0)
    cap = bankroll * max_bankroll_fraction
    if min_order_size > cap:
        return 0.0
    size = min(bankroll * f * frac, cap)
    if size < min_order_size:
        return 0.0
    if not math.isfinite(size) or not math.isfinite(max_order_size):
        return 0.0
    return round(min(max_order_size, size), 2)

def adverse_gate(adverse_ewma_bps: Optional[float], mid: Optional[float], edge: float) -> bool:
    if adverse_ewma_bps is None or mid is None or mid <= 0:
        return False
    if adverse_ewma_bps <= 0.0:
        return False
    adverse_per_share = adverse_ewma_bps / 10000.0 * mid
    return adverse_per_share >= max(0.0, edge)

def maker_entry_price(best_bid: Optional[float], best_ask: Optional[float], tick: float, join_ticks: int, prob_cap: float) -> Optional[float]:
    if best_bid is None or best_bid <= 0 or tick <= 0:
        return None
    price = best_bid + max(0, join_ticks) * tick
    if best_ask is not None and best_ask > 0:
        price = min(price, best_ask - tick)
    price = min(price, prob_cap - tick)
    price = math.floor(round(price / tick, 9)) * tick
    if price <= 0.0 or price >= 1.0:
        return None
    return round(price, 6)

def _ev_sell_now(p_side: float, bid_net: float, buffer: float=0.0, salvage_floor: float=0.0) -> bool:
    if bid_net <= 0.0:
        return False
    if salvage_floor > 0.0 and bid_net < salvage_floor:
        return True
    return bid_net >= p_side + max(0.0, buffer)

def should_force_exit_near_expiry(side_is_yes: bool, p_up: float, hold_if_winning: bool, hold_prob: float, bid_net: float=0.0, ev_exit_buffer: float=0.0, salvage_floor: float=0.0) -> bool:
    if not hold_if_winning:
        return True
    p_side = p_up if side_is_yes else 1.0 - p_up
    if p_side < hold_prob:
        return True
    return _ev_sell_now(p_side, bid_net, ev_exit_buffer, salvage_floor)

@dataclass
class CalibrationReport:
    n_trades: int
    n_eval_rows: int
    brier: Optional[float]
    realized_hit_rate: Optional[float]
    mean_ask: Optional[float]
    mean_entry_slip: Optional[float]
    realized_edge_net_cost: Optional[float]
    mean_net_pnl: Optional[float]
    total_net_pnl: Optional[float]
    mean_adverse_bps: Optional[float]
    reliability: List[Tuple[float, float, int]]

def _to_float(v: Any) -> Optional[float]:
    if v is None:
        return None
    s = str(v).strip()
    if s == '':
        return None
    try:
        f = float(s)
        return f if math.isfinite(f) else None
    except (TypeError, ValueError):
        return None

def load_calibration_rows(path: str) -> List[Dict[str, str]]:
    expanded = os.path.expanduser(path)
    if not expanded or not os.path.exists(expanded):
        return []
    rows: List[Dict[str, str]] = []
    with open(expanded, newline='', encoding='utf-8') as fh:
        for row in csv.DictReader(fh):
            if row:
                rows.append(row)
    return rows

def build_matched_samples(rows: List[Dict[str, str]]) -> List[Dict[str, Any]]:
    evals_by_mkt: Dict[str, List[Dict[str, Any]]] = {}
    outcomes: List[Dict[str, Any]] = []
    for row in rows:
        rt = (row.get('row_type') or '').strip()
        mid = (row.get('market_id') or '').strip()
        ts = _to_float(row.get('ts_unix')) or 0.0
        strategy = (row.get('strategy') or '').strip().lower()
        outcome_kind = (row.get('outcome_kind') or '').strip().lower()
        if rt == 'eval' and mid and (strategy == 'directional'):
            evals_by_mkt.setdefault(mid, []).append({'ts': ts, 'p': _to_float(row.get('p')), 'ask': _to_float(row.get('ask')), 'entry_slip': _to_float(row.get('entry_slip')), 'side': (row.get('side') or '').strip(), 'coin': (row.get('coin') or '').strip()})
        elif rt == 'outcome' and mid and (strategy == 'directional') and (outcome_kind == 'final'):
            outcomes.append({'ts': ts, 'mid': mid, 'win': _to_float(row.get('win')), 'net_pnl': _to_float(row.get('net_pnl')), 'side': (row.get('side') or '').strip()})
    for evs in evals_by_mkt.values():
        evs.sort(key=lambda e: e['ts'])
    matched: List[Dict[str, Any]] = []
    for o in outcomes:
        cands = [e for e in evals_by_mkt.get(o['mid'], []) if e['ts'] <= o['ts'] and e['p'] is not None and (e['side'] == o.get('side', ''))]
        if not cands:
            continue
        e = cands[-1]
        matched.append({'p': e['p'], 'ask': e['ask'], 'entry_slip': e['entry_slip'], 'win': o['win'], 'net_pnl': o['net_pnl'], 'coin': e.get('coin', ''), 'side': o.get('side', '')})
    return matched

def calibration_report(rows: List[Dict[str, str]]) -> CalibrationReport:
    matched = build_matched_samples(rows)
    n_eval = sum((1 for r in rows if (r.get('row_type') or '').strip() == 'eval' and (r.get('strategy') or '').strip().lower() == 'directional'))
    adverse = [v for v in (_to_float(r.get('adverse_bps')) for r in rows if (r.get('row_type') or '').strip() == 'shadow') if v is not None]
    mean_adverse = sum(adverse) / len(adverse) if adverse else None
    wins = [m for m in matched if m['win'] is not None]
    if not wins:
        return CalibrationReport(n_trades=len(matched), n_eval_rows=n_eval, brier=None, realized_hit_rate=None, mean_ask=None, mean_entry_slip=None, realized_edge_net_cost=None, mean_net_pnl=None, total_net_pnl=None, mean_adverse_bps=mean_adverse, reliability=[])
    n = len(wins)
    hit_rate = sum((m['win'] for m in wins)) / n
    with_p = [m for m in wins if m['p'] is not None]
    brier = sum(((m['p'] - m['win']) ** 2 for m in with_p)) / len(with_p) if with_p else None
    asks = [m['ask'] for m in wins if m['ask'] is not None]
    slips = [m['entry_slip'] for m in wins if m['entry_slip'] is not None]
    mean_ask = sum(asks) / len(asks) if asks else None
    mean_slip = sum(slips) / len(slips) if slips else 0.0
    per_trade_edges = [m['win'] - m['ask'] - (m['entry_slip'] if m['entry_slip'] is not None else 0.0) for m in wins if m['ask'] is not None]
    edge_net = sum(per_trade_edges) / len(per_trade_edges) if per_trade_edges else None
    pnls = [m['net_pnl'] for m in wins if m['net_pnl'] is not None]
    mean_pnl = sum(pnls) / len(pnls) if pnls else None
    total_pnl = sum(pnls) if pnls else None
    buckets: Dict[int, List[float]] = {}
    for m in with_p:
        b = min(19, int(m['p'] / 0.05))
        buckets.setdefault(b, []).append(m['win'])
    reliability = [(round(b * 0.05, 2), sum(v) / len(v), len(v)) for b, v in sorted(buckets.items())]
    return CalibrationReport(n_trades=len(matched), n_eval_rows=n_eval, brier=brier, realized_hit_rate=hit_rate, mean_ask=mean_ask, mean_entry_slip=mean_slip, realized_edge_net_cost=edge_net, mean_net_pnl=mean_pnl, total_net_pnl=total_pnl, mean_adverse_bps=mean_adverse, reliability=reliability)

def go_no_go(report: CalibrationReport, *, min_samples: int, min_edge: float, max_adverse_bps: float) -> Tuple[bool, List[str]]:
    reasons: List[str] = []
    if report.n_trades < min_samples:
        reasons.append(f'insufficient samples: {report.n_trades} closed trades < required {min_samples}')
    if report.realized_edge_net_cost is None:
        reasons.append('no realized edge measurable (no matched outcomes)')
    elif report.realized_edge_net_cost <= min_edge:
        reasons.append(f"realized edge net of cost {report.realized_edge_net_cost:+.4f} <= required {min_edge:+.4f} (the model's selected trades did NOT beat the price they paid)")
    if report.mean_net_pnl is not None and report.mean_net_pnl <= 0.0:
        reasons.append(f'mean net PnL per trade {report.mean_net_pnl:+.4f} <= 0')
    if report.mean_adverse_bps is not None and report.mean_adverse_bps > max_adverse_bps:
        reasons.append(f'adverse selection {report.mean_adverse_bps:.1f}bps > cap {max_adverse_bps:.1f}bps (you are the dumb liquidity)')
    return (not reasons, reasons)

def print_calibration_report(report: CalibrationReport, path: str) -> None:

    def fmt(v: Optional[float], spec: str='+.4f') -> str:
        return 'n/a' if v is None else format(v, spec)
    print('\n=== Polybot calibration report ===')
    print(f'source            : {os.path.expanduser(path)}')
    print(f'eval rows         : {report.n_eval_rows}')
    print(f'closed trades     : {report.n_trades}')
    print(f"realized hit rate : {fmt(report.realized_hit_rate, '.4f')}")
    print(f"mean entry ask    : {fmt(report.mean_ask, '.4f')}")
    print(f"mean entry slip   : {fmt(report.mean_entry_slip, '.4f')}")
    print(f'edge net of cost  : {fmt(report.realized_edge_net_cost)}   (hit_rate - ask - slip; >0 means real edge)')
    print(f"Brier score       : {fmt(report.brier, '.4f')}   (lower is better; 0.25 = coin flip)")
    print(f'mean net PnL/trade : {fmt(report.mean_net_pnl)}')
    print(f'total net PnL     : {fmt(report.total_net_pnl)}')
    print(f"adverse selection : {fmt(report.mean_adverse_bps, '.1f')} bps   (post-fill mid drift against us)")
    if report.reliability:
        print('\nreliability (predicted bucket -> realized win rate):')
        for lo, rate, k in report.reliability:
            print(f'  [{lo:.2f},{lo + 0.05:.2f})  win={rate:.3f}  n={k}')
    print('')

class FiveMinStrategy:

    def __init__(self, cfg: Config, om: OrderManager, risk: 'Risk', tracker: PriceTracker, metrics: Optional[Metrics]=None):
        self.cfg = cfg
        self.om = om
        self.risk = risk
        self.tracker = tracker
        self.metrics = metrics
        self.log = get_logger('FiveMinStrat', cfg.log_level)
        self._traded: Set[str] = set()
        self.measure_only: bool = False
        self._open_prices: Dict[str, float] = {}
        self._open_intervals: Dict[str, int] = {}
        self._high_bids: Dict[Any, float] = {}
        self._fast_exit_counts: Dict[Any, int] = {}
        self._trail_breach_counts: Dict[Any, int] = {}
        self._net_exposure: float = 0.0
        self._gross_exposure: float = 0.0
        self._pending_entry: Dict[Tuple[str, str], float] = {}
        self._realized_loss: Dict[str, float] = {}
        self._sustain_counts: Dict[str, int] = {}
        self._entry_times: Dict[str, float] = {}
        self._no_open_price_counts: Dict[str, int] = {}
        self._open_price_warned: Set[str] = set()
        self._rest_open_last: Dict[str, float] = {}
        self._raw_entry_px: Dict[Tuple[str, str], float] = {}
        self._tp1_taken: Dict[Tuple[str, str], float] = {}
        self._entry_edges: Dict[Tuple[str, str], float] = {}
        self._shares_in_flight: Dict[Tuple[str, str], float] = {}
        self._exit_fail_counts: Dict[Tuple[str, str], int] = {}
        self._pending_redemptions: Dict[Tuple[str, str], Tuple[float, float, float]] = {}
        self._redeem_meta: Dict[Tuple[str, str], Dict[str, Any]] = {}
        self._calib_entry_meta: Dict[Tuple[str, str], Dict[str, Any]] = {}
        self.redeemer: Optional[Any] = None
        self.polyfeed: Optional[Any] = None
        self._balance_cache: float = 0.0
        self._balance_ts: float = 0.0
        self._balance_gen: int = 0
        self._balance_force_refresh: bool = False
        self._last_capital_shock_mono: float = 0.0
        self._capital_shock_cancel_cooldown_s: float = 30.0
        self._eval_debounce: Dict[str, float] = {}
        self._recent_outcomes: Deque[bool] = deque(maxlen=50)
        self._recent_wins: int = 0
        self._per_coin_outcomes: Dict[str, Deque[bool]] = {}
        self._per_coin_wins: Dict[str, int] = {}
        self._eval_sem = asyncio.Semaphore(cfg.max_concurrent_evals)
        self._diag_guard_hits: int = 0
        self._diag_eval_reached: int = 0
        self._diag_last_summary: float = time.monotonic()
        self._diag_trigger_calls: int = 0
        self._calib_fh: Optional[Any] = None
        self._calib_init_done: bool = False
        self._calib_writes: int = 0
        self._calib_pool = concurrent.futures.ThreadPoolExecutor(max_workers=1, thread_name_prefix='calib-io')
        self._settlement_ledger: Dict[str, dict] = {}
        self._market_lookup: Optional[Callable[[str], Optional['Market']]] = None
        self._trade_pnl_in_flight_ref: Optional[Dict[Tuple[str, str], float]] = None
        self.on_state_change: Optional[Callable[[], None]] = None

    def _notify_state(self) -> None:
        if self.on_state_change is not None:
            self.on_state_change()

    def free_cash(self) -> float:
        pending = sum(self._pending_entry.values())
        return max(0.0, self._balance_cache - pending)

    def note_cash_mutation(self) -> None:
        self._balance_gen += 1

    def exposure_caps(self) -> Tuple[float, float]:
        free = max(0.0, self._balance_cache)
        net_cap = min(self.cfg.max_net_exposure_usdc, free * self.cfg.max_net_bankroll_mult)
        gross_cap = min(self.cfg.max_gross_exposure_usdc, free * self.cfg.max_gross_bankroll_mult)
        return (max(0.0, net_cap), max(0.0, gross_cap))

    def in_capital_shock_cooldown(self) -> bool:
        if self._last_capital_shock_mono <= 0.0:
            return False
        return time.monotonic() - self._last_capital_shock_mono < self._capital_shock_cancel_cooldown_s

    def apply_authoritative_balance(self, new_bal: float, *, expected_gen: Optional[int]=None) -> Tuple[bool, str]:
        if expected_gen is not None and self._balance_gen != expected_gen:
            self._balance_force_refresh = True
            self.log.info('Balance snapshot discarded (stale gen: got %d, live %d) â€” keeping local free-cash $%.2f', expected_gen, self._balance_gen, self._balance_cache)
            return (False, 'stale_discarded')
        new_bal = max(0.0, float(new_bal))
        old = self._balance_cache
        had_prior = self._balance_ts > 0
        self._balance_cache = new_bal
        self._balance_ts = time.time()
        self._balance_gen += 1
        self._balance_force_refresh = False
        if not had_prior:
            return (False, 'boot')
        drop = old - new_bal
        if drop <= 0.0:
            return (False, 'applied')
        thresh = max(self.cfg.capital_shock_floor_usdc, old * self.cfg.capital_shock_pct)
        if drop + 1e-09 < thresh:
            return (False, 'applied')
        self._last_capital_shock_mono = time.monotonic()
        self.log.critical('CAPITAL SHOCK: free cash $%.2f -> $%.2f (drop $%.2f >= thresh $%.2f) â€” external debit (withdraw/transfer). Resting BUY risk cancelled; SELL exits preserved; sizing rebased to residual free cash.', old, new_bal, drop, thresh)
        return (True, 'applied')

    async def evaluate_all(self, markets: List[Market]) -> None:
        """Resync the shared exposure accumulators LatArb's caps read.

        The directional (bidirectional) entry fan-out that used to run here was
        retired; only the exposure resync is kept because _net_exposure /
        _gross_exposure are otherwise maintained incrementally (Bot._on_fill,
        _settle_resolved_market) and this is their only periodic drift check.
        """
        self._net_exposure = sum((m.pos_yes.cost - m.pos_no.cost for m in markets))
        self._gross_exposure = sum((m.pos_yes.cost + m.pos_no.cost for m in markets))

    async def _evaluate(self, mkt: Market) -> None:
        raise RuntimeError('directional (bidirectional) strategy is retired; _evaluate has no callers')

    async def _evaluate_deprecated(self, mkt: Market) -> None:
        self._diag_guard_hits += 1
        periodic = time.monotonic() - self._diag_last_summary > 90
        if periodic:
            self._diag_last_summary = time.monotonic()
            self.log.info('DIAG | calls=%d | markets=%d | traded=%d | open_prices=%d', self._diag_guard_hits, len(self.polyfeed._token_set) // 2 if self.polyfeed else 0, len(self._traded), len(self._open_prices))
            # DIAG is log-only â€” never return early (that skipped hold-to-expiry / redeem).
            try:
                if not mkt.coin or not mkt.end_time:
                    self.log.info('DIAG NOTE: no_coin_or_end_time')
                elif mkt.start_time is None:
                    self.log.info('DIAG NOTE: no_start_time | end=%s', mkt.end_time)
                else:
                    elapsed = time.time() - mkt.start_time
                    ttc = mkt.end_time - time.time()
                    is_5min = mkt.tf_secs <= 300
                    min_elapsed = max(60, self.cfg.entry_start_s) if not is_5min else self.cfg.entry_start_s
                    buffer_s = max(0, mkt.tf_secs - int(self.cfg.entry_end_s * mkt.tf_secs / 300))
                    has_pos = mkt.pos_yes.shares > 1e-06 or mkt.pos_no.shares > 1e-06
                    if elapsed < min_elapsed and (not has_pos):
                        self.log.info('DIAG NOTE: min_elapsed | %.0fs < %ds | coin=%s', elapsed, min_elapsed, mkt.coin)
                    if ttc < buffer_s and (not has_pos):
                        self.log.info('DIAG NOTE: entry_buffer | ttc=%.0f < buf=%d (positions still managed)', ttc, buffer_s)
                    binance_age = self.tracker.feed.price_age_s(mkt.coin)
                    if binance_age > 2.0:
                        self.log.info('DIAG NOTE: binance_stale | coin=%s age=%.1fs', mkt.coin, binance_age)
                    ya = mkt.book_yes.best_ask if mkt.book_yes else None
                    na = mkt.book_no.best_ask if mkt.book_no else None
                    self.log.info('DIAG SNAP | coin=%s el=%.0f ttc=%.0f has_pos=%s ya=%s na=%s', mkt.coin, elapsed, ttc, has_pos, ya, na)
            except Exception as de:
                self.log.info('DIAG ERROR: %s', de)
        try:
            await self._evaluate_core(mkt)
        except Exception as e:
            if periodic:
                self.log.warning('EVAL EXCEPTION: %s', e)
            self.log.debug("Eval exception '%s': %s", mkt.question[:30], e)

    async def _evaluate_core(self, mkt: Market) -> None:
        if not mkt.coin or not mkt.end_time:
            return
        if mkt.end_time and mkt.end_time < time.time():
            for tracked in list(self.om._orders.values()):
                if tracked.token_id in (mkt.yes_token, mkt.no_token):
                    try:
                        _ct = asyncio.create_task(self.om.cancel(tracked.order_id))
                        self.om._bg_tasks.add(_ct)
                        _ct.add_done_callback(self.om._bg_tasks.discard)
                    except RuntimeError:
                        pass
        tf_secs = float(mkt.tf_secs)
        is_5min = tf_secs <= 300.0
        now = time.time()
        interval_start = mkt.start_time
        if interval_start is None:
            return
        elapsed = now - interval_start
        ttc = mkt.end_time - now if mkt.end_time else tf_secs - elapsed
        if elapsed < 0:
            return
        if ttc < 0:
            self.log.debug('SKIP expired market %s (ttc=%.0fs, end_time in the past) â€” not evaluated', mkt.coin, ttc)
            return
        interval_epoch = int(interval_start)
        prev_interval = self._open_intervals.get(mkt.market_id)
        if prev_interval is not None and prev_interval != interval_epoch:
            self._open_prices.pop(mkt.market_id, None)
            if mkt.pos_yes.shares < 1e-06 and mkt.pos_no.shares < 1e-06:
                self._traded.discard(mkt.market_id)
            self._sustain_counts.pop(mkt.market_id, None)
            self._entry_times.pop(mkt.market_id, None)
            for hk in [k for k in self._high_bids if isinstance(k, tuple) and k[0] == mkt.market_id]:
                self._high_bids.pop(hk, None)
            for bk in [k for k in self._trail_breach_counts if isinstance(k, tuple) and k[0] == mkt.market_id]:
                self._trail_breach_counts.pop(bk, None)
        self._open_intervals[mkt.market_id] = interval_epoch
        # Positions known immediately â€” entry-window guards must NOT block hold/redeem.
        has_pos_early = mkt.pos_yes.shares > 1e-06 or mkt.pos_no.shares > 1e-06
        min_elapsed = max(60, self.cfg.entry_start_s) if not is_5min else self.cfg.entry_start_s
        entry_end_scaled = int(self.cfg.entry_end_s * tf_secs / 300)
        buffer_s = max(0, int(tf_secs) - entry_end_scaled)
        # P0: only skip NEW entries outside window; open legs still managed through expiry.
        if not has_pos_early:
            if elapsed < min_elapsed:
                return
            if ttc < buffer_s:
                return
        # P0: LatArb hold-to-settlement â€” register redeem meta before entry-buffer / stale-book gates
        # would previously return (ttc < 40s buffer blocked ttc < 25s redeem path).
        if has_pos_early and ttc < self.cfg.forced_exit_ttc_s:
            def _is_latarb_tok(tid: str) -> bool:
                toks = getattr(mkt, 'latarb_hold_tokens', set()) or set()
                if tid in toks:
                    return True
                tag = self.om.get_entry_strategy(tid) if self.om is not None else None
                return tag == 'latarb' or (bool(getattr(mkt, 'latarb_hold', False)) and not toks)
            if mkt.pos_yes.shares > 1e-06 and _is_latarb_tok(mkt.yes_token):
                self._mark_for_redemption(mkt, mkt.yes_token, mkt.pos_yes, 1.0)
            if mkt.pos_no.shares > 1e-06 and _is_latarb_tok(mkt.no_token):
                self._mark_for_redemption(mkt, mkt.no_token, mkt.pos_no, 1.0)
            # Directional near-expiry still needs books/model below; LatArb is done.
            only_latarb = True
            if mkt.pos_yes.shares > 1e-06 and (not _is_latarb_tok(mkt.yes_token)):
                only_latarb = False
            if mkt.pos_no.shares > 1e-06 and (not _is_latarb_tok(mkt.no_token)):
                only_latarb = False
            if only_latarb:
                return
        binance_age = self.tracker.feed.price_age_s(mkt.coin)
        if binance_age > 2.0 and (not has_pos_early):
            return
        current_price = self.tracker.feed.price(mkt.coin, max_age_s=2.0)
        if not current_price:
            if not has_pos_early:
                return
            # Inventory path may continue with last hist price for exit math only.
            hist = self.tracker._history.get(mkt.coin) if self.tracker else None
            current_price = hist[-1][1] if hist else 0.0
            if current_price <= 0:
                return
        if mkt.market_id not in self._open_prices:
            open_price = self.tracker.get_price_at_or_before(str(mkt.coin), interval_start, max_lag_s=10.0)
            if open_price is None:
                _c = mkt.coin or '?'
                _now_rest = time.monotonic()
                if _now_rest - self._rest_open_last.get(_c, 0.0) >= 3.0:
                    self._rest_open_last[_c] = _now_rest
                    try:
                        _symbol = f'{mkt.coin}USDT'
                        _start_ms = int(interval_start * 1000)
                        _url = f'https://api.binance.com/api/v3/klines?symbol={_symbol}&interval=1m&startTime={_start_ms}&limit=1'
                        async with aiohttp.ClientSession() as _s:
                            async with _s.get(_url, timeout=aiohttp.ClientTimeout(total=3)) as _r:
                                if _r.status == 200:
                                    _data = await _r.json()
                                    if _data and len(_data) > 0:
                                        open_price = float(_data[0][1])
                                        self.log.info('OPEN-PRICE REST fallback: %s @ %.4f', mkt.coin, open_price)
                    except Exception:
                        pass
            if open_price is None:
                c = mkt.coin or '?'
                n = self._no_open_price_counts.get(c, 0) + 1
                self._no_open_price_counts[c] = n
                if n == 20 and c not in self._open_price_warned:
                    self._open_price_warned.add(c)
                    self.log.critical('OPEN-PRICE FAILURE: %s has had no interval anchor for %d consecutive evals (interval_start=%.0f, now=%.0f). No %s trades can fire until the price feed / clock is fixed.  Check Binance connectivity and discovery timing.', c, n, interval_start, now, c)
                elif n == 3 and c not in self._open_price_warned:
                    self.log.warning('no_open_price %s: %d consecutive misses (hist may be cold or feed lagging). interval_start=%.0f', c, n, interval_start)
                else:
                    self.log.debug('no_open_price %s: miss #%d (interval_start=%.0f)', c, n, interval_start)
                return
            c = mkt.coin or '?'
            if c in self._no_open_price_counts:
                self._no_open_price_counts.pop(c, None)
            if c in self._open_price_warned:
                self._open_price_warned.discard(c)
                self.log.info('OPEN-PRICE OK: %s anchor recovered', c)
            self._open_prices[mkt.market_id] = open_price
        open_price = self._open_prices[mkt.market_id]
        tau_s = max(1.0, ttc)
        if not mkt.fresh_books(self.cfg.book_max_age_ms):
            return
        yes_ask = mkt.book_yes.best_ask if mkt.book_yes else None
        no_ask = mkt.book_no.best_ask if mkt.book_no else None
        btc_disp = None
        if mkt.coin != 'BTC':
            btc_price = self.tracker.feed.price('BTC', max_age_s=2.0)
            btc_open = self.tracker.get_price_at_or_before('BTC', interval_start, max_lag_s=10.0)
            if btc_price and btc_open and (btc_open > 0):
                btc_disp = (btc_price - btc_open) / btc_open
        yes_trade = self.polyfeed.last_trade(mkt.yes_token) if self.polyfeed else None
        p_up = self.tracker.prob_up(mkt.coin, current_price, open_price, tau_s, yes_book=mkt.book_yes, yes_trade_ewma=yes_trade, btc_displacement=btc_disp)
        p_model_raw = p_up
        w_anc = self.cfg.market_anchor_weight
        p_market_est: Optional[float] = None
        yes_mid_v = mkt.book_yes.mid if mkt.book_yes else None
        no_mid_v = mkt.book_no.mid if mkt.book_no else None
        mkt_estimates = []
        if yes_mid_v and 0 < yes_mid_v < 1:
            mkt_estimates.append(yes_mid_v)
        if no_mid_v and 0 < no_mid_v < 1:
            mkt_estimates.append(1.0 - no_mid_v)
        if not mkt_estimates and (yes_ask or no_ask):
            if yes_ask and 0 < yes_ask < 1:
                mkt_estimates.append(yes_ask)
            if no_ask and 0 < no_ask < 1:
                mkt_estimates.append(1.0 - no_ask)
        if mkt_estimates:
            p_market_est = sum(mkt_estimates) / len(mkt_estimates)
        if w_anc > 0.0 and p_market_est is not None:
            p_up = (1.0 - w_anc) * p_up + w_anc * p_market_est
            p_up = max(0.02, min(0.98, p_up))
        skip_for_disagreement = False
        if self.cfg.max_model_disagreement > 0.0 and p_market_est is not None and (abs(p_model_raw - p_market_est) > self.cfg.max_model_disagreement):
            skip_for_disagreement = True
        if self.cfg.anchor_edge_path:
            p_up_edge = p_up
        else:
            p_up_edge = max(0.02, min(0.98, p_model_raw))
        has_yes = mkt.pos_yes.shares > 1e-06
        has_no = mkt.pos_no.shares > 1e-06
        managed_leg = False

        def _bid_net(gross_bid: Optional[float]) -> float:
            if not gross_bid or gross_bid <= 0.0:
                return 0.0
            if self.cfg.category_fee_rate > 0:
                return gross_bid - self.cfg.category_fee_rate * gross_bid * (1.0 - gross_bid)
            return gross_bid - self.cfg.taker_fee_bps * 0.0001 * gross_bid
        if ttc < self.cfg.forced_exit_ttc_s and (has_yes or has_no):
            # F4: LatArb edge is hold-to-settlement â€” never force-sell via directional p_up.
            def _is_latarb_token(tid: str) -> bool:
                toks = getattr(mkt, 'latarb_hold_tokens', set()) or set()
                if tid in toks:
                    return True
                return bool(getattr(mkt, 'latarb_hold', False)) and not toks
            if has_yes:
                if _is_latarb_token(mkt.yes_token):
                    self._mark_for_redemption(mkt, mkt.yes_token, mkt.pos_yes, p_up)
                else:
                    yes_bid = mkt.book_yes.best_bid if mkt.book_yes and mkt.book_yes.best_bid else 0.0
                    if should_force_exit_near_expiry(True, p_up, self.cfg.forced_exit_hold_if_winning, self.cfg.forced_exit_hold_prob, bid_net=_bid_net(yes_bid), ev_exit_buffer=self.cfg.ev_exit_buffer, salvage_floor=self.cfg.salvage_floor):
                        bid = yes_bid if yes_bid > 0 else 0.01
                        await self._execute_exit(mkt, mkt.yes_token, bid, 'EXPIRY_YES', mkt.pos_yes.shares)
                    else:
                        self._mark_for_redemption(mkt, mkt.yes_token, mkt.pos_yes, p_up)
            if has_no:
                if _is_latarb_token(mkt.no_token):
                    self._mark_for_redemption(mkt, mkt.no_token, mkt.pos_no, 1.0 - p_up)
                else:
                    no_bid = mkt.book_no.best_bid if mkt.book_no and mkt.book_no.best_bid else 0.0
                    if should_force_exit_near_expiry(False, p_up, self.cfg.forced_exit_hold_if_winning, self.cfg.forced_exit_hold_prob, bid_net=_bid_net(no_bid), ev_exit_buffer=self.cfg.ev_exit_buffer, salvage_floor=self.cfg.salvage_floor):
                        bid = no_bid if no_bid > 0 else 0.01
                        await self._execute_exit(mkt, mkt.no_token, bid, 'EXPIRY_NO', mkt.pos_no.shares)
                    else:
                        self._mark_for_redemption(mkt, mkt.no_token, mkt.pos_no, 1.0 - p_up)
            return
        entry_mono = self._entry_times.get(mkt.market_id)
        if entry_mono and time.monotonic() - entry_mono < 60:
            drop_mult = 1.0 - self.cfg.fast_exit_drop_pct
            for held, token, book, pos, label in ((has_yes, mkt.yes_token, mkt.book_yes, mkt.pos_yes, 'FAST_YES'), (has_no, mkt.no_token, mkt.book_no, mkt.pos_no, 'FAST_NO')):
                if not (held and book and book.micro_price):
                    continue
                fkey = (mkt.market_id, token)
                entry_ref = self._raw_entry_px.get(fkey) or pos.avg_price
                if book.micro_price < entry_ref * drop_mult:
                    cnt = self._fast_exit_counts.get(fkey, 0) + 1
                    self._fast_exit_counts[fkey] = cnt
                    if cnt >= self.cfg.fast_exit_sustain:
                        self._fast_exit_counts.pop(fkey, None)
                        bid = book.best_bid or 0.01
                        self.log.info('FAST-EXIT %s %s | micro=%.3f < entry*%.2f (x%d)', label, mkt.coin, book.micro_price, drop_mult, cnt)
                        await self._execute_exit(mkt, token, bid, label, pos.shares)
                        return
                else:
                    self._fast_exit_counts.pop(fkey, None)
        if has_yes:
            bid = mkt.book_yes.best_bid if mkt.book_yes else None
            micro = mkt.book_yes.micro_price if mkt.book_yes else None
            trail_val = micro if micro else bid
            if trail_val is None or trail_val <= 0:
                return
            if mkt.book_yes is None or mkt.book_yes.is_stale(self.cfg.book_max_age_ms):
                return
            if bid is None:
                bid = trail_val
            tp_key = (mkt.market_id, mkt.yes_token)
            in_flight_yes = self._shares_in_flight.get(tp_key, 0.0)
            if in_flight_yes > 0 and (not self.om.find_open(mkt.yes_token, Side.SELL)):
                self._shares_in_flight.pop(tp_key, None)
                in_flight_yes = 0.0
            effective_yes = max(0.0, mkt.pos_yes.shares - in_flight_yes)
            if effective_yes >= 1e-06:
                managed_leg = True
                if (mkt.yes_token in getattr(mkt, 'latarb_hold_tokens', set()) or (getattr(mkt, 'latarb_hold', False) and (not getattr(mkt, 'latarb_hold_tokens', set())))) and ttc > self.cfg.forced_exit_ttc_s:
                    pass
                elif _ev_sell_now(p_up, _bid_net(bid), self.cfg.ev_exit_buffer, self.cfg.salvage_floor):
                    fail_cnt = self._exit_fail_counts.get(tp_key, 0)
                    if fail_cnt >= 5:
                        self.log.warning('STOP_YES %s: %d FOK failures, escalating to GTC', mkt.coin, fail_cnt)
                        await self._execute_exit(mkt, mkt.yes_token, bid, 'STOP_YES_GTC', effective_yes)
                        return
                    open_sell = self.om.find_open(mkt.yes_token, Side.SELL)
                    if open_sell is not None:
                        await self.om.cancel(open_sell.order_id)
                    self._high_bids.pop(tp_key, None)
                    self._tp1_taken.pop(tp_key, None)
                    self._entry_edges.pop(tp_key, None)
                    self._shares_in_flight.pop(tp_key, None)
                    await self._execute_exit(mkt, mkt.yes_token, bid, 'STOP_YES', mkt.pos_yes.shares)
                else:
                    entry_px = mkt.pos_yes.avg_price
                    tp_fired = False
                    if self.cfg.partial_tp_enabled and tp_key not in self._tp1_taken and (entry_px > 0):
                        tp_bid_px = bid if bid and bid > 0 else trail_val
                        gain_ratio = (tp_bid_px - entry_px) / entry_px
                        if self.cfg.tp_mode == 'fixed':
                            if gain_ratio >= self.cfg.tp1_pct:
                                clip_pct = self.cfg.tp1_clip_pct
                                tp_fired = True
                        else:
                            cur_edge = p_up - trail_val
                            entry_edge = self._entry_edges.get(tp_key, 0.05)
                            edge_decayed = cur_edge < entry_edge * 0.5
                            if edge_decayed and gain_ratio > 0.01:
                                conf = self._compute_confidence(tp_key, entry_px, trail_val, cur_edge, mkt)
                                clip_pct = min(self.cfg.conf_max_clip, max(self.cfg.conf_min_clip, conf * self.cfg.conf_scale))
                                tp_fired = True
                        if tp_fired:
                            clip_shares = math.floor(effective_yes * clip_pct)
                            if clip_shares >= 1.0 and clip_shares * (bid or 0.01) >= 0.5:
                                self._tp1_taken[tp_key] = entry_px
                                self._sustain_counts.pop(mkt.market_id, None)
                                self._shares_in_flight[tp_key] = in_flight_yes + clip_shares
                                mode_tag = 'C' if self.cfg.tp_mode == 'confidence' else 'F'
                                self.log.info('TP1_YES[%s] %s | entry=%.3f bid=%.3f gain=+%.1f%% | clip=%d/%d (%.0f%%)', mode_tag, mkt.coin, entry_px, tp_bid_px, gain_ratio * 100, int(clip_shares), int(effective_yes), clip_pct * 100)
                                await self._execute_exit(mkt, mkt.yes_token, bid, 'TP1_YES', clip_shares)
                    elif tp_key in self._tp1_taken and self.cfg.tp1_breakeven_stop:
                        if _ev_sell_now(p_up, _bid_net(bid), self.cfg.ev_exit_buffer, self.cfg.salvage_floor):
                            self._tp1_taken.pop(tp_key, None)
                            self._high_bids.pop(tp_key, None)
                            self._entry_edges.pop(tp_key, None)
                            self._shares_in_flight.pop(tp_key, None)
                            self.log.info('BE_STOP_YES %s | p_up=%.3f bid_net=%.3f trail=%.3f', mkt.coin, p_up, _bid_net(bid), trail_val)
                            await self._execute_exit(mkt, mkt.yes_token, bid, 'BE_STOP_YES', effective_yes)
                        else:
                            trail_key = tp_key
                            prev_high = self._high_bids.get(trail_key, 0.0)
                            if trail_val > prev_high:
                                self._high_bids[trail_key] = trail_val
                                self._trail_breach_counts.pop(trail_key, None)
                            else:
                                breached = prev_high >= self.cfg.trail_arm_level and trail_val <= prev_high * (1.0 - self.cfg.trail_stop_pct)
                                if self._trail_should_fire(trail_key, breached):
                                    self._high_bids.pop(trail_key, None)
                                    self._tp1_taken.pop(tp_key, None)
                                    self._entry_edges.pop(tp_key, None)
                                    self._shares_in_flight.pop(tp_key, None)
                                    await self._execute_exit(mkt, mkt.yes_token, bid, 'TRAIL_YES', effective_yes)
                    else:
                        trail_key = tp_key
                        prev_high = self._high_bids.get(trail_key, 0.0)
                        if trail_val > prev_high:
                            self._high_bids[trail_key] = trail_val
                            self._trail_breach_counts.pop(trail_key, None)
                        else:
                            breached = prev_high >= self.cfg.trail_arm_level and trail_val <= prev_high * (1.0 - self.cfg.trail_stop_pct)
                            if self._trail_should_fire(trail_key, breached):
                                self._high_bids.pop(trail_key, None)
                                self._entry_edges.pop(trail_key, None)
                                self._shares_in_flight.pop(trail_key, None)
                                await self._execute_exit(mkt, mkt.yes_token, bid, 'TRAIL_YES', effective_yes)
        if has_no:
            bid = mkt.book_no.best_bid if mkt.book_no else None
            micro = mkt.book_no.micro_price if mkt.book_no else None
            trail_val = micro if micro else bid
            if trail_val is None or trail_val <= 0:
                return
            if mkt.book_no is None or mkt.book_no.is_stale(self.cfg.book_max_age_ms):
                return
            if bid is None:
                bid = trail_val
            p_down = 1.0 - p_up
            tp_key = (mkt.market_id, mkt.no_token)
            in_flight_no = self._shares_in_flight.get(tp_key, 0.0)
            if in_flight_no > 0 and (not self.om.find_open(mkt.no_token, Side.SELL)):
                self._shares_in_flight.pop(tp_key, None)
                in_flight_no = 0.0
            effective_no = max(0.0, mkt.pos_no.shares - in_flight_no)
            if effective_no >= 1e-06:
                managed_leg = True
                if (mkt.no_token in getattr(mkt, 'latarb_hold_tokens', set()) or (getattr(mkt, 'latarb_hold', False) and (not getattr(mkt, 'latarb_hold_tokens', set())))) and ttc > self.cfg.forced_exit_ttc_s:
                    pass
                elif _ev_sell_now(p_down, _bid_net(bid), self.cfg.ev_exit_buffer, self.cfg.salvage_floor):
                    fail_cnt = self._exit_fail_counts.get(tp_key, 0)
                    if fail_cnt >= 5:
                        self.log.warning('STOP_NO %s: %d FOK failures, escalating to GTC', mkt.coin, fail_cnt)
                        await self._execute_exit(mkt, mkt.no_token, bid, 'STOP_NO_GTC', effective_no)
                        return
                    open_sell = self.om.find_open(mkt.no_token, Side.SELL)
                    if open_sell is not None:
                        await self.om.cancel(open_sell.order_id)
                    self._high_bids.pop(tp_key, None)
                    self._tp1_taken.pop(tp_key, None)
                    self._entry_edges.pop(tp_key, None)
                    self._shares_in_flight.pop(tp_key, None)
                    await self._execute_exit(mkt, mkt.no_token, bid, 'STOP_NO', mkt.pos_no.shares)
                else:
                    entry_px = mkt.pos_no.avg_price
                    tp_fired = False
                    if self.cfg.partial_tp_enabled and tp_key not in self._tp1_taken and (entry_px > 0):
                        tp_bid_px = bid if bid and bid > 0 else trail_val
                        gain_ratio = (tp_bid_px - entry_px) / entry_px
                        if self.cfg.tp_mode == 'fixed':
                            if gain_ratio >= self.cfg.tp1_pct:
                                clip_pct = self.cfg.tp1_clip_pct
                                tp_fired = True
                        else:
                            cur_edge = 1.0 - p_up - trail_val
                            entry_edge = self._entry_edges.get(tp_key, 0.05)
                            edge_decayed = cur_edge < entry_edge * 0.5
                            if edge_decayed and gain_ratio > 0.01:
                                conf = self._compute_confidence(tp_key, entry_px, trail_val, cur_edge, mkt)
                                clip_pct = min(self.cfg.conf_max_clip, max(self.cfg.conf_min_clip, conf * self.cfg.conf_scale))
                                tp_fired = True
                        if tp_fired:
                            clip_shares = math.floor(effective_no * clip_pct)
                            if clip_shares >= 1.0 and clip_shares * (bid or 0.01) >= 0.5:
                                self._tp1_taken[tp_key] = entry_px
                                self._sustain_counts.pop(mkt.market_id, None)
                                self._shares_in_flight[tp_key] = in_flight_no + clip_shares
                                mode_tag = 'C' if self.cfg.tp_mode == 'confidence' else 'F'
                                self.log.info('TP1_NO[%s] %s | entry=%.3f bid=%.3f gain=+%.1f%% | clip=%d/%d (%.0f%%)', mode_tag, mkt.coin, entry_px, tp_bid_px, gain_ratio * 100, int(clip_shares), int(effective_no), clip_pct * 100)
                                await self._execute_exit(mkt, mkt.no_token, bid, 'TP1_NO', clip_shares)
                    elif tp_key in self._tp1_taken and self.cfg.tp1_breakeven_stop:
                        if _ev_sell_now(p_down, _bid_net(bid), self.cfg.ev_exit_buffer, self.cfg.salvage_floor):
                            self._tp1_taken.pop(tp_key, None)
                            self._high_bids.pop(tp_key, None)
                            self._entry_edges.pop(tp_key, None)
                            self._shares_in_flight.pop(tp_key, None)
                            self.log.info('BE_STOP_NO %s | p_down=%.3f bid_net=%.3f trail=%.3f', mkt.coin, p_down, _bid_net(bid), trail_val)
                            await self._execute_exit(mkt, mkt.no_token, bid, 'BE_STOP_NO', effective_no)
                        else:
                            trail_key = tp_key
                            prev_high = self._high_bids.get(trail_key, 0.0)
                            if trail_val > prev_high:
                                self._high_bids[trail_key] = trail_val
                                self._trail_breach_counts.pop(trail_key, None)
                            else:
                                breached = prev_high >= self.cfg.trail_arm_level and trail_val <= prev_high * (1.0 - self.cfg.trail_stop_pct)
                                if self._trail_should_fire(trail_key, breached):
                                    self._high_bids.pop(trail_key, None)
                                    self._tp1_taken.pop(tp_key, None)
                                    self._entry_edges.pop(tp_key, None)
                                    self._shares_in_flight.pop(tp_key, None)
                                    await self._execute_exit(mkt, mkt.no_token, bid, 'TRAIL_NO', effective_no)
                    else:
                        trail_key = tp_key
                        prev_high = self._high_bids.get(trail_key, 0.0)
                        if trail_val > prev_high:
                            self._high_bids[trail_key] = trail_val
                            self._trail_breach_counts.pop(trail_key, None)
                        else:
                            breached = prev_high >= self.cfg.trail_arm_level and trail_val <= prev_high * (1.0 - self.cfg.trail_stop_pct)
                            if self._trail_should_fire(trail_key, breached):
                                self._high_bids.pop(trail_key, None)
                                self._entry_edges.pop(trail_key, None)
                                self._shares_in_flight.pop(trail_key, None)
                                await self._execute_exit(mkt, mkt.no_token, bid, 'TRAIL_NO', effective_no)
        if managed_leg:
            return
        if mkt.market_id in self._traded and (not has_yes) and (not has_no) and (not self.om.find_open(mkt.yes_token, Side.BUY)) and (not self.om.find_open(mkt.no_token, Side.BUY)):
            self._pending_entry.pop((mkt.market_id, mkt.yes_token), None)
            self._pending_entry.pop((mkt.market_id, mkt.no_token), None)
        for token in (mkt.yes_token, mkt.no_token):
            stale = self.om.find_open(token, Side.BUY)
            if stale and time.monotonic() - stale.created > 45:
                await self.om.cancel(stale.order_id)
                self._traded.discard(mkt.market_id)
                _ck = (mkt.market_id, token)
                if _ck in self._pending_entry:
                    self._pending_entry.pop(_ck, None)
        if self.om.find_open(mkt.yes_token, Side.BUY) or self.om.find_open(mkt.no_token, Side.BUY):
            return
        if yes_ask is None or no_ask is None:
            return
        if self.cfg.category_fee_rate > 0:
            fee_y = self.cfg.category_fee_rate * yes_ask * (1.0 - yes_ask)
            fee_n = self.cfg.category_fee_rate * no_ask * (1.0 - no_ask)
        else:
            fee_y = self.cfg.taker_fee_bps * 0.0001 * yes_ask
            fee_n = self.cfg.taker_fee_bps * 0.0001 * no_ask
        arb_cost = yes_ask + no_ask + fee_y + fee_n
        arb_edge = 1.0 - arb_cost
        if self.cfg.complement_arb_enabled and arb_edge > 2 * self.cfg.min_edge and (yes_ask > 0.01) and (no_ask > 0.01):
            if not self.risk.ok():
                return
            self.log.info('COMPLEMENT_ARB %s | YES=%.3f + NO=%.3f = %.3f | edge=%.4f', mkt.coin, yes_ask, no_ask, yes_ask + no_ask, arb_edge)
            arb_size = min(self.cfg.max_order_size, self.cfg.max_bankroll_fraction * (self.free_cash() if self._balance_ts > 0 else self.cfg.max_order_size * 2))
            if arb_size >= self.cfg.min_order_size:
                _pending_total = sum(self._pending_entry.values())
                _, _gross_cap = self.exposure_caps()
                if self._gross_exposure + arb_size + _pending_total > _gross_cap:
                    self.log.info('COMPLEMENT_ARB skip %s: gross cap (exp=%.1f + arb=%.1f + pending=%.1f > max=%.1f)', mkt.coin, self._gross_exposure, arb_size, _pending_total, _gross_cap)
                    return
                self._traded.add(mkt.market_id)
                tick_y = mkt.get_tick(mkt.yes_token)
                tick_n = mkt.get_tick(mkt.no_token)
                _rk_y = (mkt.market_id, mkt.yes_token)
                _rk_n = (mkt.market_id, mkt.no_token)
                _half = arb_size / 2.0
                self._pending_entry[_rk_y] = self._pending_entry.get(_rk_y, 0.0) + _half
                self._pending_entry[_rk_n] = self._pending_entry.get(_rk_n, 0.0) + _half
                oid_y = await self.om.place(mkt.yes_token, Side.BUY, yes_ask, _half, Strategy.TEMPORAL, otype='FOK', neg_risk=mkt.neg_risk, tick_size=tick_y, quote_ts=mkt.book_yes.ts if mkt.book_yes else None, max_quote_age_ms=self.cfg.book_max_age_ms)
                oid_n = await self.om.place(mkt.no_token, Side.BUY, no_ask, _half, Strategy.TEMPORAL, otype='FOK', neg_risk=mkt.neg_risk, tick_size=tick_n, quote_ts=mkt.book_no.ts if mkt.book_no else None, max_quote_age_ms=self.cfg.book_max_age_ms)
                if oid_y or oid_n:
                    self._entry_times[mkt.market_id] = time.monotonic()
                if not oid_y:
                    self._pending_entry[_rk_y] = max(0.0, self._pending_entry.get(_rk_y, 0.0) - _half)
                    if self._pending_entry.get(_rk_y, 0.0) < 1e-09:
                        self._pending_entry.pop(_rk_y, None)
                if not oid_n:
                    self._pending_entry[_rk_n] = max(0.0, self._pending_entry.get(_rk_n, 0.0) - _half)
                    if self._pending_entry.get(_rk_n, 0.0) < 1e-09:
                        self._pending_entry.pop(_rk_n, None)
                if not oid_y and (not oid_n):
                    self._traded.discard(mkt.market_id)
            return
        if self.tracker.is_choppy(mkt.coin, int(tf_secs)):
            return
        for book in (mkt.book_yes, mkt.book_no):
            if book and (book.top_depth_usdc < self.cfg.min_top_book_usdc or book.spread_pct > self.cfg.max_spread_pct):
                return
        for book in (mkt.book_yes, mkt.book_no):
            if book and book.best_bid and (book.best_bid < 0.03):
                return
        spread_yes = mkt.book_yes.spread_pct if mkt.book_yes else 0.0
        spread_no = mkt.book_no.spread_pct if mkt.book_no else 0.0
        spread_pct = max(spread_yes, spread_no)
        sigma_per_sec = self.tracker.volatility(mkt.coin) if mkt.coin else 0.0
        ttc_eff = max(1.0, mkt.end_time - time.time()) if mkt.end_time else 60.0
        sigma_h = sigma_per_sec * math.sqrt(ttc_eff)
        ask_for_floor = yes_ask or no_ask or 0.5
        if self.cfg.category_fee_rate > 0 and ask_for_floor > 0:
            _fee_floor = self.cfg.category_fee_rate * ask_for_floor * (1.0 - ask_for_floor)
        else:
            _fee_floor = self.cfg.taker_fee_bps * 0.0001 * ask_for_floor
        taker_delay_buffer = 0.0
        if self.cfg.entry_mode == 'taker' and sigma_per_sec > 0:
            taker_delay_buffer = min(2.0 * self.cfg.min_edge, sigma_per_sec * math.sqrt(0.25))
        req_edge = max(self.cfg.min_edge, _fee_floor + self.cfg.min_edge_margin + taker_delay_buffer, spread_pct * self.cfg.spread_edge_mult, sigma_h * self.cfg.sigma_edge_mult)
        vel = self.tracker.velocity(mkt.coin, window_s=30)
        if p_up >= 0.5:
            if has_yes:
                return
            if self.polyfeed and time.monotonic() < self.polyfeed._last_large_trade_ts.get(mkt.yes_token, 0.0) + self.cfg.whale_cooldown_s:
                self.log.info('SKIP ENTRY %s UP: recent whale trade, settling', mkt.coin)
                return
            if yes_ask is None or yes_ask > 0.85:
                return
            if btc_disp is not None and btc_disp < -0.003:
                return
            if vel < -0.0004:
                return
            entry_per_share, exit_per_share, fillable = self._round_trip_cost(mkt.book_yes, self.cfg.min_order_size)
            if not fillable:
                return
            entry_slip = max(0.0, entry_per_share - yes_ask)
            exit_slip = max(0.0, 1.0 - exit_per_share) if exit_per_share > 0 else 0.0
            if self.cfg.category_fee_rate > 0:
                fee = self.cfg.category_fee_rate * yes_ask * (1.0 - yes_ask)
            else:
                fee = self.cfg.taker_fee_bps * 0.0001 * yes_ask
            edge = p_up_edge - yes_ask - entry_slip - fee
            raw_edge = p_model_raw - yes_ask - entry_slip - fee if p_model_raw is not None else None
            disagree = abs(p_model_raw - p_market_est) if p_model_raw is not None and p_market_est is not None else None
            self.log.info('EVAL UP %s | el=%3.0fs | p=%.3f | edge=%.3f | raw_edge=%.3f | disagree=%.3f | ask=%.3f | es=%.4f xs=%.4f fee=%.4f', mkt.coin, elapsed, p_up, edge, raw_edge if raw_edge is not None else float('nan'), disagree if disagree is not None else float('nan'), yes_ask, entry_slip, exit_slip, fee)
            self._log_prediction(mkt, 'UP', p_up, yes_ask, edge, entry_slip, exit_slip, p_model_raw=p_model_raw, p_market=p_market_est)
            if edge >= req_edge:
                if skip_for_disagreement:
                    self.log.info('SKIP ENTRY %s UP: model-mkt disagreement %.3f > %.3f (p_model=%.3f vs mkt=%.3f)', mkt.coin, abs(p_model_raw - (p_market_est or 0.5)), self.cfg.max_model_disagreement, p_model_raw, p_market_est or 0.0)
                else:
                    sc = self._sustain_counts.get(mkt.market_id, 0) + 1
                    self._sustain_counts[mkt.market_id] = sc
                    if sc < self.cfg.sustain_ticks:
                        self.log.info('SUSTAIN %s UP: %d/%d', mkt.coin, sc, self.cfg.sustain_ticks)
                        return
                    self._sustain_counts[mkt.market_id] = 0
                    _net_cap, _gross_cap = self.exposure_caps()
                    if self._net_exposure + self.cfg.min_order_size > _net_cap:
                        return
                    if self._gross_exposure + self.cfg.min_order_size > _gross_cap:
                        return
                    await self._place_sliced(mkt, mkt.yes_token, yes_ask, 'UP', p_up, edge, entry_slip, exit_slip, req_edge=req_edge)
        else:
            p_down = 1.0 - p_up
            p_down_edge = 1.0 - p_up_edge
            if has_yes:
                return
            if self.polyfeed and time.monotonic() < self.polyfeed._last_large_trade_ts.get(mkt.no_token, 0.0) + self.cfg.whale_cooldown_s:
                self.log.info('SKIP ENTRY %s DN: recent whale trade, settling', mkt.coin)
                return
            if p_down >= 0.5:
                if no_ask is None or no_ask > 0.85:
                    return
                if btc_disp is not None and btc_disp > 0.003:
                    return
                if vel > 0.0004:
                    return
                entry_per_share, exit_per_share, fillable = self._round_trip_cost(mkt.book_no, self.cfg.min_order_size)
                if not fillable:
                    return
                entry_slip = max(0.0, entry_per_share - no_ask)
                exit_slip = max(0.0, 1.0 - exit_per_share) if exit_per_share > 0 else 0.0
                if self.cfg.category_fee_rate > 0:
                    fee = self.cfg.category_fee_rate * no_ask * (1.0 - no_ask)
                else:
                    fee = self.cfg.taker_fee_bps * 0.0001 * no_ask
                edge = p_down_edge - no_ask - entry_slip - fee
                raw_down = 1.0 - p_model_raw if p_model_raw is not None else None
                raw_edge = raw_down - no_ask - entry_slip - fee if raw_down is not None else None
                disagree = abs(p_model_raw - p_market_est) if p_model_raw is not None and p_market_est is not None else None
                self.log.info('EVAL DN %s | el=%3.0fs | p=%.3f | edge=%.3f | raw_edge=%.3f | disagree=%.3f | ask=%.3f | es=%.4f xs=%.4f fee=%.4f', mkt.coin, elapsed, p_down, edge, raw_edge if raw_edge is not None else float('nan'), disagree if disagree is not None else float('nan'), no_ask, entry_slip, exit_slip, fee)
                self._log_prediction(mkt, 'DN', p_down, no_ask, edge, entry_slip, exit_slip, p_model_raw=p_model_raw, p_market=p_market_est)
                if edge >= req_edge:
                    if skip_for_disagreement:
                        self.log.info('SKIP ENTRY %s DN: model-mkt disagreement %.3f > %.3f (p_model=%.3f vs mkt=%.3f)', mkt.coin, abs(p_model_raw - (p_market_est or 0.5)), self.cfg.max_model_disagreement, p_model_raw, p_market_est or 0.0)
                    else:
                        sc = self._sustain_counts.get(mkt.market_id, 0) + 1
                        self._sustain_counts[mkt.market_id] = sc
                        if sc < self.cfg.sustain_ticks:
                            self.log.info('SUSTAIN %s DN: %d/%d', mkt.coin, sc, self.cfg.sustain_ticks)
                            return
                        self._sustain_counts[mkt.market_id] = 0
                        _net_cap, _gross_cap = self.exposure_caps()
                        if self._net_exposure - self.cfg.min_order_size < -_net_cap:
                            return
                        if self._gross_exposure + self.cfg.min_order_size > _gross_cap:
                            return
                        await self._place_sliced(mkt, mkt.no_token, no_ask, 'DN', p_down, edge, entry_slip, exit_slip, req_edge=req_edge)
            else:
                self._sustain_counts.pop(mkt.market_id, None)

    def _trail_should_fire(self, trail_key: Any, breached: bool) -> bool:
        if not breached:
            self._trail_breach_counts.pop(trail_key, None)
            return False
        cnt = self._trail_breach_counts.get(trail_key, 0) + 1
        self._trail_breach_counts[trail_key] = cnt
        if cnt >= self.cfg.trail_sustain:
            self._trail_breach_counts.pop(trail_key, None)
            return True
        return False

    def _round_trip_cost(self, book: Optional[OrderBook], size_usdc: float) -> Tuple[float, float, bool]:
        return _round_trip_cost(book, size_usdc)

    def _fok_sweep_price(self, book: Optional[OrderBook], size_usdc: float, tick: float, dec: int, mt: int) -> float:
        return _fok_sweep_price(book, size_usdc, tick, dec, mt)

    async def _place_sliced(self, mkt: Market, token_id: str, ask_price: float, label: str, prob: float, edge: float, entry_slip: float=0.0, exit_slip: float=0.0, req_edge: float=0.0) -> None:
        if self.measure_only and (not self.cfg.dry_run):
            self.log.debug('MEASURE-ONLY (LIVE): suppressed %s entry %s (p=%.3f edge=%.3f ask=%.3f) â€” no proven edge, no order placed.', label, mkt.coin, prob, edge, ask_price)
            return
        if self.measure_only and self.cfg.dry_run:
            self.log.debug('MEASURE-ONLY (DRY): allowing paper trade %s %s (p=%.3f edge=%.3f ask=%.3f) â€” collecting outcome data for go/no-go gate.', label, mkt.coin, prob, edge, ask_price)
        if req_edge <= 0.0:
            req_edge = self.cfg.min_edge
        if not self.risk.ok():
            return
        if self.in_capital_shock_cooldown() and (not self.cfg.dry_run):
            return
        if mkt.market_id in self._traded:
            return
        if self.cfg.adverse_select_gate:
            book0 = mkt.book_yes if token_id == mkt.yes_token else mkt.book_no
            mid0 = book0.mid if book0 else None
            _adv = self.om.adverse_ewma('directional')
            if adverse_gate(_adv, mid0, edge):
                self.log.info('SKIP ENTRY %s %s: adverse EWMA %+.1fbps eats edge %.3f', label, mkt.coin, _adv or 0.0, edge)
                return
        book = mkt.book_yes if token_id == mkt.yes_token else mkt.book_no
        _, exit_vwap, _ = self._round_trip_cost(book, self.cfg.max_order_size)
        exit_slip = max(0.0, 1.0 - exit_vwap) if exit_vwap > 0 else exit_slip
        kelly_sz = self._kelly_size(prob, ask_price, entry_slip, exit_slip, coin=mkt.coin)
        if kelly_sz <= 0.0:
            self.log.info('SKIP ENTRY %s %s: min clip exceeds %.0f%% bankroll cap ($%.2f free cash) â€” account too small to size safely', label, mkt.coin, self.cfg.max_bankroll_fraction * 100.0, self.free_cash() if self._balance_ts > 0 else self.cfg.max_order_size * 2)
            return
        _afford = self.free_cash() if self._balance_ts > 0 else kelly_sz
        if not self.cfg.dry_run and kelly_sz > _afford + 1e-09:
            kelly_sz = math.floor(_afford * 100.0) / 100.0
            if kelly_sz < self.cfg.min_order_size:
                self.log.info('SKIP ENTRY %s %s: unaffordable (need >=$%.2f, free $%.2f)', label, mkt.coin, self.cfg.min_order_size, _afford)
                return
        tick = mkt.get_tick(token_id)
        dec, mt = mkt.tick_math(token_id)
        book = mkt.book_yes if token_id == mkt.yes_token else mkt.book_no
        if book is None or book.is_stale(self.cfg.book_max_age_ms):
            self.log.info('SKIP ENTRY %s %s: book stale before placement', label, mkt.coin)
            return
        cur_ask = book.best_ask
        if cur_ask is None:
            self.log.info('SKIP ENTRY %s %s: no live ask at placement', label, mkt.coin)
            return
        if abs(cur_ask - ask_price) > tick:
            self.log.info('SKIP ENTRY %s %s: ask moved %+.4f since eval (tick=%.4f)', label, mkt.coin, cur_ask - ask_price, tick)
            return
        if self.cfg.category_fee_rate > 0:
            _gate_fee = self.cfg.category_fee_rate * ask_price * (1.0 - ask_price)
        else:
            _gate_fee = self.cfg.taker_fee_bps * 0.0001 * ask_price

        def _exec_edge_at(s: float) -> Optional[float]:
            e_entry, _, ok = self._round_trip_cost(book, s)
            if not ok:
                return None
            return prob - ask_price - max(0.0, e_entry - ask_price) - _gate_fee
        top_edge = _exec_edge_at(kelly_sz)
        if top_edge is not None and top_edge >= req_edge:
            sz = kelly_sz
        else:
            lo, hi = (self.cfg.min_order_size, kelly_sz)
            hi = max(hi, lo)
            base_edge = _exec_edge_at(lo)
            if base_edge is None or base_edge < req_edge:
                self.log.info('SKIP ENTRY %s %s: edge %.4f < req_edge %.4f even at $%.1f min clip', label, mkt.coin, base_edge if base_edge is not None else float('nan'), req_edge, lo)
                return
            best = lo
            for _ in range(12):
                mid = 0.5 * (lo + hi)
                em = _exec_edge_at(mid)
                if em is not None and em >= req_edge:
                    best, lo = (mid, mid)
                else:
                    hi = mid
            sz = best
            self.log.info('SIZE-DOWN %s %s: Kelly $%.1f â†’ $%.1f to hold edge â‰¥ %.4f', label, mkt.coin, kelly_sz, sz, req_edge)
        if sz < self.cfg.min_order_size:
            return
        if mkt.total_cost + sz > self.cfg.max_position:
            return
        if self._realized_loss.get(mkt.market_id, 0.0) <= -self.cfg.max_position:
            self.log.warning('SKIP ENTRY %s %s: realized loss $%.2f on this market has reached the max_position cap $%.2f â€” refusing new entries (likely overlapping-interval accumulation; investigate).', label, mkt.coin, self._realized_loss.get(mkt.market_id, 0.0), self.cfg.max_position)
            return
        _is_yes = token_id == mkt.yes_token
        _pending_total = sum(self._pending_entry.values())
        _net_cap, _gross_cap = self.exposure_caps()
        if _is_yes:
            if self._net_exposure + sz + _pending_total > _net_cap:
                return
        elif self._net_exposure - sz - _pending_total < -_net_cap:
            return
        if self._gross_exposure + sz + _pending_total > _gross_cap:
            return
        if self.cfg.entry_mode == 'maker':
            maker_px = maker_entry_price(book.best_bid if book else None, book.best_ask if book else None, tick, self.cfg.maker_join_ticks, prob)
            if maker_px is None:
                self.log.info('SKIP ENTRY %s %s: no valid maker price (bid=%s ask=%s)', label, mkt.coin, book.best_bid if book else None, book.best_ask if book else None)
                return
            self.log.info('ENTRY(maker) %s %s | P=%.3f | edge=%.3f | post=%.4f | sz=$%.1f', label, mkt.coin, prob, edge, maker_px, sz)
            self._traded.add(mkt.market_id)
            _rkey = (mkt.market_id, token_id)
            self._pending_entry[_rkey] = self._pending_entry.get(_rkey, 0.0) + sz
            oid = await self.om.place(token_id, Side.BUY, maker_px, sz, Strategy.TEMPORAL, otype='GTC', neg_risk=mkt.neg_risk, tick_size=tick, quote_ts=book.ts if book else None, max_quote_age_ms=self.cfg.book_max_age_ms)
            if oid:
                self._entry_times[mkt.market_id] = time.monotonic()
                self._entry_edges[mkt.market_id, token_id] = edge
                self._raw_entry_px[mkt.market_id, token_id] = maker_px
            else:
                self._traded.discard(mkt.market_id)
                self._pending_entry[_rkey] = max(0.0, self._pending_entry.get(_rkey, 0.0) - sz)
                if self._pending_entry.get(_rkey, 0.0) < 1e-09:
                    self._pending_entry.pop(_rkey, None)
            return
        sweep_price = self._fok_sweep_price(book, sz, tick, dec, mt)
        if sweep_price <= 0:
            return
        if sweep_price > 0.82:
            self.log.info('SKIP ENTRY %s %s: sweep %.4f > 0.82 cap', label, mkt.coin, sweep_price)
            return
        sweep_fee = _gate_fee if abs(sweep_price - ask_price) < tick else self.cfg.category_fee_rate * sweep_price * (1.0 - sweep_price) if self.cfg.category_fee_rate > 0 else self.cfg.taker_fee_bps * 0.0001 * sweep_price
        sweep_edge = prob - sweep_price - sweep_fee
        if sweep_edge < req_edge:
            self.log.info('SKIP FOK %s %s: sweep erodes edge to %.4f < req_edge %.4f (sweep=%.4f vs ask=%.4f)', label, mkt.coin, sweep_edge, req_edge, sweep_price, ask_price)
            return
        self.log.info('ENTRY %s %s | P=%.3f | edge=%.3f | price=%.4f | sz=$%.1f', label, mkt.coin, prob, edge, sweep_price, sz)
        self._traded.add(mkt.market_id)
        _rkey = (mkt.market_id, token_id)
        self._pending_entry[_rkey] = self._pending_entry.get(_rkey, 0.0) + sz
        oid = await self.om.place(token_id, Side.BUY, sweep_price, sz, Strategy.TEMPORAL, otype='FOK', neg_risk=mkt.neg_risk, tick_size=tick, quote_ts=book.ts if book else None, max_quote_age_ms=self.cfg.book_max_age_ms)
        if oid:
            self._entry_times[mkt.market_id] = time.monotonic()
            self._entry_edges[mkt.market_id, token_id] = edge
            self._raw_entry_px[mkt.market_id, token_id] = sweep_price
        else:
            self._traded.discard(mkt.market_id)
            self._pending_entry[_rkey] = max(0.0, self._pending_entry.get(_rkey, 0.0) - sz)
            if self._pending_entry.get(_rkey, 0.0) < 1e-09:
                self._pending_entry.pop(_rkey, None)

    def register_latarb_fill_for_settle(self, mkt: 'Market', token_id: str, shares: float, fill_px: float, fee: float=0.0) -> None:
        """P0: register settlement/redeem meta on every confirmed LatArb fill (not only near expiry)."""
        if shares < 1e-09 or fill_px <= 0:
            return
        rkey = (mkt.market_id, token_id)
        cost_add = float(fill_px) * float(shares) + max(0.0, float(fee))
        is_yes = token_id == mkt.yes_token
        open_px = float(self._open_prices.get(mkt.market_id, 0.0) or 0.0)
        end_ts = float(mkt.end_time) if getattr(mkt, 'end_time', None) else 0.0
        if rkey in self._redeem_meta:
            meta = self._redeem_meta[rkey]
            meta['shares'] = float(meta.get('shares', 0.0)) + float(shares)
            meta['cost'] = float(meta.get('cost', 0.0)) + cost_add
            avg = meta['cost'] / max(meta['shares'], 1e-09)
            meta['est_pnl'] = (1.0 - avg) * meta['shares']  # soft win-side estimate only
            if open_px > 0:
                meta['open_price'] = open_px
            if end_ts > 0:
                meta['end_time'] = end_ts
            self._pending_redemptions[rkey] = (meta['shares'], avg, 1.0)
            self.log.info('LATARB_SETTLE_META add %s %s | sh=+%.4f tot=%.4f cost=$%.4f', mkt.coin, 'UP' if is_yes else 'DN', shares, meta['shares'], meta['cost'])
            return
        avg = cost_add / max(float(shares), 1e-09)
        est = (1.0 - avg) * float(shares)
        self._pending_redemptions[rkey] = (float(shares), avg, 1.0)
        self._redeem_meta[rkey] = {
            'condition_id': getattr(mkt, 'condition_id', '') or '',
            'neg_risk': bool(getattr(mkt, 'neg_risk', False)),
            'is_yes': is_yes,
            'token_id': token_id,
            'yes_token': mkt.yes_token,
            'no_token': mkt.no_token,
            'shares': float(shares),
            'cost': cost_add,
            'est_pnl': est,
            'coin': mkt.coin,
            'strategy': 'latarb',
            'open_price': open_px,
            'end_time': end_ts,
            'source': 'fill',
        }
        # Do NOT soft-book assumed win into Risk PnL (est = full win). That inflates
        # peak then DD-halts on loss correction (realized-est). Settle writes realized only.
        self._redeem_meta[rkey]['risk_soft_booked'] = False
        self.log.info('LATARB_SETTLE_META new %s %s | sh=%.4f avg=%.4f cost=$%.4f est=$%.4f (risk PnL deferred to settle)', mkt.coin, 'UP' if is_yes else 'DN', shares, avg, cost_add, est)

    def _mark_for_redemption(self, mkt: 'Market', token_id: str, pos: 'Position', expected_payout: float) -> None:
        rkey = (mkt.market_id, token_id)
        shares = pos.shares
        avg_price = pos.avg_price
        if shares < 1e-06 or avg_price <= 0:
            return
        expected_pnl = (expected_payout - avg_price) * shares
        cost = avg_price * shares
        is_latarb = token_id in getattr(mkt, 'latarb_hold_tokens', set()) or bool(getattr(mkt, 'latarb_hold', False)) or (self.om.get_entry_strategy(token_id) if self.om else None) == 'latarb'
        if rkey in self._pending_redemptions:
            # Already registered on fill â€” refresh sizes from live position; do not double soft PnL.
            meta = self._redeem_meta.get(rkey) or {}
            meta.update({'shares': shares, 'cost': cost, 'est_pnl': expected_pnl, 'condition_id': getattr(mkt, 'condition_id', '') or meta.get('condition_id', ''), 'neg_risk': bool(getattr(mkt, 'neg_risk', False)), 'is_yes': token_id == mkt.yes_token, 'token_id': token_id, 'yes_token': mkt.yes_token, 'no_token': mkt.no_token, 'coin': mkt.coin, 'strategy': 'latarb' if is_latarb else 'directional'})
            self._redeem_meta[rkey] = meta
            self._pending_redemptions[rkey] = (shares, avg_price, expected_payout)
            self.log.info('HOLD_TO_EXPIRY refresh %s %s | shares=%.4f avg=%.4f est=$%.2f', mkt.coin, 'YES' if token_id == mkt.yes_token else 'NO', shares, avg_price, expected_pnl)
            return
        self._pending_redemptions[rkey] = (shares, avg_price, expected_payout)
        self._redeem_meta[rkey] = {'condition_id': getattr(mkt, 'condition_id', '') or '', 'neg_risk': bool(getattr(mkt, 'neg_risk', False)), 'is_yes': token_id == mkt.yes_token, 'token_id': token_id, 'yes_token': mkt.yes_token, 'no_token': mkt.no_token, 'shares': shares, 'cost': cost, 'est_pnl': expected_pnl, 'coin': mkt.coin, 'strategy': 'latarb' if is_latarb else 'directional', 'open_price': self._open_prices.get(mkt.market_id, 0.0), 'source': 'hold'}
        self.risk.record_pnl(expected_pnl)
        self.log.info('HOLD_TO_EXPIRY %s %s | shares=%.1f avg=%.4f E[payout]=%.2f est_pnl=$%.2f (marked for redemption; settles via resolve)', mkt.coin, 'YES' if token_id == mkt.yes_token else 'NO', shares, avg_price, expected_payout, expected_pnl)

    def _compute_confidence(self, tp_key: Tuple[str, str], entry_px: float, trail_val: float, current_edge: float, mkt: 'Market') -> float:
        if entry_px <= 0 or trail_val <= 0:
            return 0.0
        p_win = max(0.01, min(0.99, trail_val + current_edge))
        ev_hold = p_win * 1.0 - entry_px
        ev_sell = trail_val - entry_px
        if tp_key not in self._entry_edges:
            return 0.0
        entry_edge = self._entry_edges[tp_key]
        edge_decay = min(1.0, max(0.0, entry_edge - current_edge) / max(entry_edge, 0.01))
        entry_ts = self._entry_times.get(mkt.market_id, time.monotonic())
        elapsed = max(0.0, time.monotonic() - entry_ts)
        end_ts = mkt.end_time
        now_w = time.time()
        if end_ts and end_ts > now_w:
            ttc = end_ts - now_w
            time_pressure = min(1.0, elapsed / max(elapsed + ttc, 1.0))
        else:
            time_pressure = min(1.0, elapsed / 300.0)
        ev_delta = ev_sell - ev_hold
        ev_component = min(1.0, max(0.0, ev_delta / max(abs(ev_hold), 0.01)))
        confidence = 0.1 * ev_component + 0.7 * edge_decay + 0.2 * time_pressure
        return max(0.0, min(1.0, confidence))

    def _kelly_size(self, prob: float, entry_price: float, entry_slip: float=0.0, exit_slip: float=0.0, coin: Optional[str]=None) -> float:
        if not 0 < prob < 1:
            return self.cfg.min_order_size
        if self.cfg.per_coin_crossover and coin and (coin in self._per_coin_outcomes):
            window = self._per_coin_outcomes[coin]
            wins_in_window = self._per_coin_wins.get(coin, 0)
        else:
            window = self._recent_outcomes
            wins_in_window = self._recent_wins
        n_recent = len(window)
        if self.cfg.adaptive_kelly and n_recent > 0:
            k_wins = wins_in_window
            p_shrunk = (k_wins + 1) / (n_recent + 2)
            w = n_recent / (n_recent + 20)
            p_blend = (1.0 - w) * prob + w * p_shrunk
            p_final = min(prob, p_blend)
        else:
            p_final = prob
        if self.cfg.dry_run:
            _min_viable = self.cfg.min_order_size / max(self.cfg.max_bankroll_fraction, 1e-09)
            bankroll = max(self.cfg.max_order_size * 2.0, _min_viable * 5.0)
        elif self._balance_ts > 0:
            bankroll = self.free_cash()
        else:
            if not self.cfg.dry_run:
                return 0.0
            bankroll = self.cfg.max_order_size * 2
        cold_start = self.cfg.adaptive_kelly and n_recent < 20
        return kelly_size(p_final, entry_price, entry_slip, exit_slip, kelly_fraction=self.cfg.kelly_fraction, bankroll=bankroll, max_bankroll_fraction=self.cfg.max_bankroll_fraction, min_order_size=self.cfg.min_order_size, max_order_size=self.cfg.max_order_size, cold_start=cold_start, negative_ev_skips=True, p_hold_to_expiry=self.cfg.kelly_hold_to_expiry_rate, taker_fee_bps=self.cfg.taker_fee_bps, category_fee_rate=self.cfg.category_fee_rate)

    def record_outcome(self, win: bool, market_id: Optional[str]=None, net_pnl: Optional[float]=None, coin: Optional[str]=None, side: str='', strategy: str='directional', outcome_kind: str='final', log_calibration: bool=True) -> None:
        win_b = bool(win)
        if len(self._recent_outcomes) == self._recent_outcomes.maxlen and self._recent_outcomes[0]:
            self._recent_wins -= 1
        self._recent_outcomes.append(win_b)
        if win_b:
            self._recent_wins += 1
        if coin:
            dq = self._per_coin_outcomes.get(coin)
            if dq is None:
                dq = deque(maxlen=30)
                self._per_coin_outcomes[coin] = dq
                self._per_coin_wins[coin] = 0
            if len(dq) == dq.maxlen and dq[0]:
                self._per_coin_wins[coin] -= 1
            dq.append(win_b)
            if win_b:
                self._per_coin_wins[coin] = self._per_coin_wins.get(coin, 0) + 1
        if market_id is not None and log_calibration:
            self._calibration_log('outcome', market_id=market_id, win=win_b, net_pnl=net_pnl, coin=coin, side=side, strategy=strategy, outcome_kind=outcome_kind)
        # Settlement-true LatArb ledger (final outcomes only; includes dry-settle + live redeem).
        if str(strategy or '').lower() == 'latarb' and str(outcome_kind or '') == 'final' and net_pnl is not None:
            _append_latarb_settle({'ts': time.time(), 'market_id': market_id or '', 'coin': coin or '', 'side': side or '', 'win': win_b, 'net_pnl': float(net_pnl), 'dry_run': bool(self.cfg.dry_run), 'source': 'settle'}, self.cfg)

    def _log_prediction(self, mkt: 'Market', side: str, p: float, ask: float, edge: float, entry_slip: float, exit_slip: float, p_model_raw: Optional[float]=None, p_market: Optional[float]=None) -> None:
        by, bn = (mkt.book_yes, mkt.book_no)
        self._calibration_log('eval', market_id=mkt.market_id, coin=getattr(mkt, 'coin', ''), side=side, p=p, ask=ask, edge=edge, entry_slip=entry_slip, exit_slip=exit_slip, yes_bid=by.best_bid if by else None, yes_ask=by.best_ask if by else None, no_bid=bn.best_bid if bn else None, no_ask=bn.best_ask if bn else None, p_model_raw=p_model_raw, p_market=p_market, strategy='directional', outcome_kind='')

    def _log_shadow(self, info: Dict[str, Any]) -> None:
        self._calibration_log('shadow', market_id=str(info.get('market_id') or ''), side=str(info.get('side') or ''), adverse_bps=info.get('adverse_bps'), strategy='probe', outcome_kind='')

    def _calibration_log(self, row_type: str, **fields: Any) -> None:
        cfg = self.cfg
        if not cfg.calibration_log_enabled or not cfg.calibration_log_path:
            return
        now = time.time()
        iso = datetime.fromtimestamp(now, tz=timezone.utc).isoformat(timespec='seconds').replace('+00:00', 'Z')
        cols = [iso, f'{now:.3f}', row_type, cfg.prob_model, str(fields.get('strategy', 'directional' if row_type == 'eval' else '')), str(fields.get('outcome_kind', '')), str(fields.get('market_id', '')), str(fields.get('coin', '')), str(fields.get('side', '')), '' if fields.get('p') is None else f"{float(fields['p']):.6f}", '' if fields.get('ask') is None else f"{float(fields['ask']):.6f}", '' if fields.get('edge') is None else f"{float(fields['edge']):.6f}", '' if fields.get('entry_slip') is None else f"{float(fields['entry_slip']):.6f}", '' if fields.get('exit_slip') is None else f"{float(fields['exit_slip']):.6f}", '' if fields.get('win') is None else '1' if fields['win'] else '0', '' if fields.get('net_pnl') is None else f"{float(fields['net_pnl']):.4f}", '' if fields.get('yes_bid') is None else f"{float(fields['yes_bid']):.6f}", '' if fields.get('yes_ask') is None else f"{float(fields['yes_ask']):.6f}", '' if fields.get('no_bid') is None else f"{float(fields['no_bid']):.6f}", '' if fields.get('no_ask') is None else f"{float(fields['no_ask']):.6f}", '' if fields.get('adverse_bps') is None else f"{float(fields['adverse_bps']):.3f}", '' if fields.get('p_model_raw') is None else f"{float(fields['p_model_raw']):.6f}", '' if fields.get('p_market') is None else f"{float(fields['p_market']):.6f}"]
        safe = [c if ',' not in c and '\n' not in c else '"' + c.replace('"', '""') + '"' for c in cols]
        line = ','.join(safe) + '\n'
        try:
            self._calib_pool.submit(self._write_calib_row, line)
        except RuntimeError:
            pass

    def _write_calib_row(self, line: str) -> None:
        try:
            f = self._calib_fh
            if f is None:
                if self._calib_init_done:
                    return
                self._calib_init_done = True
                primary = os.path.expanduser(self.cfg.calibration_log_path)
                base = os.path.basename(primary) or 'calibration.csv'
                candidates = [primary, os.path.expanduser(os.path.join('~', base)), os.path.join(os.getcwd(), base)]
                header = 'ts_iso,ts_unix,row_type,model,strategy,outcome_kind,market_id,coin,side,p,ask,edge,entry_slip,exit_slip,win,net_pnl,yes_bid,yes_ask,no_bid,no_ask,adverse_bps,p_model_raw,p_market\n'
                f = None
                path = primary
                for cand in candidates:
                    try:
                        os.makedirs(os.path.dirname(cand) or '.', exist_ok=True)
                        if os.path.exists(cand) and os.path.getsize(cand) > 0:
                            expected_cols = header.strip().count(',') + 1
                            corrupt_rows = False
                            with open(cand, 'r', encoding='utf-8') as _rf:
                                existing_hdr = _rf.readline()
                                if existing_hdr.strip() == header.strip():
                                    for _ in range(200):
                                        sample = _rf.readline()
                                        if not sample:
                                            break
                                        if sample.strip() and sample.rstrip('\n').count(',') + 1 != expected_cols:
                                            corrupt_rows = True
                                            break
                            if existing_hdr.strip() != header.strip() or corrupt_rows:
                                bak = '%s.bak.%d' % (cand, int(time.time() * 1000))
                                os.replace(cand, bak)
                                self.log.warning('Calibration schema changed/corrupt; rotated stale log %s -> %s (started fresh with new header)', cand, bak)
                        f = open(cand, 'a', encoding='utf-8')
                    except OSError:
                        continue
                    if cand != primary:
                        self.log.warning('Calibration log path %s not writable; falling back to %s', primary, cand)
                    path = cand
                    break
                if f is None:
                    self.log.warning('Calibration logging DISABLED: no writable path (tried %s)', candidates)
                    return
                need_header = not os.path.exists(path) or os.path.getsize(path) == 0
                self._calib_fh = f
                if need_header:
                    f.write(header)
            f.write(line)
            self._calib_writes += 1
            if self._calib_writes % _CALIB_FLUSH_EVERY == 0:
                f.flush()
        except Exception as e:
            self.log.warning('Calibration log write failed: %s', e)

    def close_calibration_log(self) -> None:
        pool = getattr(self, '_calib_pool', None)
        if pool is not None:
            pool.shutdown(wait=True)
        fh = self._calib_fh
        if fh is not None and (not fh.closed):
            try:
                fh.flush()
                fh.close()
            except Exception as e:
                self.log.warning('Calibration log close failed: %s', e)
        self._calib_fh = None

    async def _execute_exit(self, mkt: Market, token_id: str, bid_price: float, label: str, shares: float) -> None:
        flight_key = (mkt.market_id, token_id)

        def _rollback_inflight() -> None:
            cur = self._shares_in_flight.get(flight_key, 0.0)
            if cur > 0:
                cur = max(0.0, cur - shares)
                if cur < 1e-06:
                    self._shares_in_flight.pop(flight_key, None)
                else:
                    self._shares_in_flight[flight_key] = cur
        if shares < 1e-06:
            _rollback_inflight()
            return
        if shares * (bid_price or 0.01) < 0.5:
            _rollback_inflight()
            return
        tick = mkt.get_tick(token_id)
        dec, mt = mkt.tick_math(token_id)
        book = mkt.book_yes if token_id == mkt.yes_token else mkt.book_no
        size_usdc = shares * (bid_price or 0.01)
        sweep_price = _fok_sweep_price_sell(book, shares, tick, dec, mt)
        if sweep_price <= 0:
            self.log.warning('EXIT %s skipped â€” insufficient bid depth', label)
            _rollback_inflight()
            return
        if sweep_price < 0.01:
            sweep_price = 0.01
        self.log.info('EXIT %s %s | price=%.4f | shares=%.1f', label, mkt.coin, sweep_price, shares)
        exit_usdc = shares * sweep_price
        gtc_oid = None
        oid = await self.om.place(token_id, Side.SELL, sweep_price, exit_usdc, Strategy.TEMPORAL, otype='FOK', neg_risk=mkt.neg_risk, tick_size=tick, quote_ts=book.ts if book else None, max_quote_age_ms=self.cfg.book_max_age_ms)
        if not oid:
            fallback_price = max(0.01, sweep_price - tick)
            fallback_usdc = shares * fallback_price
            if fallback_usdc >= 0.5:
                gtc_oid = await self.om.place(token_id, Side.SELL, fallback_price, fallback_usdc, Strategy.TEMPORAL, otype='GTC', neg_risk=mkt.neg_risk, tick_size=tick, quote_ts=book.ts if book else None, max_quote_age_ms=self.cfg.book_max_age_ms)
                if gtc_oid:
                    self.log.info('GTC_FALLBACK %s %s | price=%.4f | shares=%.1f (FOK killed, posted limit)', label, mkt.coin, fallback_price, shares)
                else:
                    _rollback_inflight()
            else:
                _rollback_inflight()
        efc_key = (mkt.market_id, token_id)
        if oid or gtc_oid:
            self._exit_fail_counts.pop(efc_key, None)
        else:
            self._exit_fail_counts[efc_key] = self._exit_fail_counts.get(efc_key, 0) + 1
        if oid and label not in ('TP1_YES', 'TP1_NO'):
            self._entry_times.pop(mkt.market_id, None)

    def settle_expired_latarb(self, markets: List[Market], now: Optional[float]=None) -> int:
        """Settle/redeem expired LatArb inventory without waiting for market removal.

        Polls redeem_meta independently of discovery: a held market that ages out of
        the active list still settles once end_time + grace is reached.
        """
        now_ts = time.time() if now is None else float(now)
        grace_s = 5.0 if self.cfg.dry_run else 300.0
        by_id = {str(m.market_id): m for m in markets}
        due: List[str] = []
        for (mid, _), meta in list(self._redeem_meta.items()):
            if str(meta.get('strategy') or '').lower() != 'latarb':
                continue
            mid_s = str(mid)
            mkt = by_id.get(mid_s)
            if mkt is None and self._market_lookup is not None:
                try:
                    mkt = self._market_lookup(mid_s)
                except Exception:
                    mkt = None
            end_t = 0.0
            if mkt is not None and getattr(mkt, 'end_time', None):
                end_t = float(mkt.end_time)
            elif meta.get('end_time'):
                try:
                    end_t = float(meta.get('end_time') or 0.0)
                except (TypeError, ValueError):
                    end_t = 0.0
            if end_t <= 0.0:
                continue
            if end_t <= now_ts - grace_s:
                due.append(mid_s)
        due_u = sorted(set(due))
        for mid in due_u:
            self._settle_resolved_market(mid)
        return len(due_u)

    def cleanup_expired(self, markets: List[Market]) -> None:
        active_ids = {m.market_id for m in markets}
        for (mid, token_id), meta in list(self._calib_entry_meta.items()):
            if mid in active_ids or (mid, token_id) in self._pending_redemptions:
                continue
            coin = meta.get('coin') or ''
            open_spot = float(meta.get('open_price') or self._open_prices.get(mid, 0.0) or 0.0)
            final_spot = self.tracker.feed.price(coin, max_age_s=10.0) if coin and self.tracker else None
            if final_spot and open_spot > 0:
                side = str(meta.get('side') or '')
                won = final_spot > open_spot if side == 'UP' else final_spot < open_spot
                self.record_outcome(won, market_id=mid, net_pnl=None, coin=coin, side=side, strategy=str(meta.get('strategy') or 'directional'), outcome_kind='final', log_calibration=True)
            else:
                self.log.debug('CALIB_FINAL_SKIP %s | no final spot/open anchor (coin=%s open=%.4f final=%r)', mid, coin, open_spot, final_spot)
            self._calib_entry_meta.pop((mid, token_id), None)
        all_tracked = set()
        for container in (self._open_prices, self._open_intervals, self._sustain_counts, self._entry_times, self._eval_debounce):
            all_tracked.update(container.keys())
        for mid in all_tracked:
            if mid not in active_ids:
                self._open_prices.pop(mid, None)
                self._open_intervals.pop(mid, None)
                self._sustain_counts.pop(mid, None)
                self._entry_times.pop(mid, None)
                self._eval_debounce.pop(mid, None)
        self._traded.intersection_update(active_ids)
        for key in list(self._pending_entry.keys()):
            if key[0] not in active_ids:
                self._pending_entry.pop(key, None)
        for key in list(self._high_bids.keys()):
            if isinstance(key, tuple) and key[0] not in active_ids:
                self._high_bids.pop(key, None)
        for key in list(self._fast_exit_counts.keys()):
            if isinstance(key, tuple) and key[0] not in active_ids:
                self._fast_exit_counts.pop(key, None)
        for key in list(self._trail_breach_counts.keys()):
            if isinstance(key, tuple) and key[0] not in active_ids:
                self._trail_breach_counts.pop(key, None)
        for key in list(self._tp1_taken.keys()):
            if isinstance(key, tuple) and key[0] not in active_ids:
                self._tp1_taken.pop(key, None)
        for key in list(self._entry_edges.keys()):
            if isinstance(key, tuple) and key[0] not in active_ids:
                self._entry_edges.pop(key, None)
        for key in list(self._raw_entry_px.keys()):
            if isinstance(key, tuple) and key[0] not in active_ids:
                self._raw_entry_px.pop(key, None)
        for key in list(self._shares_in_flight.keys()):
            if isinstance(key, tuple) and key[0] not in active_ids:
                self._shares_in_flight.pop(key, None)
        for key in list(self._exit_fail_counts.keys()):
            if isinstance(key, tuple) and key[0] not in active_ids:
                self._exit_fail_counts.pop(key, None)
        resolved_mids: Set[str] = set()
        for key in list(self._pending_redemptions.keys()):
            if isinstance(key, tuple) and key[0] not in active_ids:
                self._pending_redemptions.pop(key, None)
                resolved_mids.add(key[0])
        for mid in resolved_mids:
            self._settle_resolved_market(mid)

    def _settle_resolved_market(self, market_id: str, winning_asset_id: Optional[str]=None) -> None:
        legs = [(k, v) for k, v in list(self._redeem_meta.items()) if k[0] == market_id]
        if not legs:
            return
        leg_keys = [k for k, _ in legs]
        meta0 = legs[0][1]
        cond_id = str(meta0.get('condition_id') or '')
        neg_risk = bool(meta0.get('neg_risk', False))
        coin = meta0.get('coin') or market_id
        strategy = str(meta0.get('strategy') or 'directional')
        est_total = sum(float(m.get('est_pnl', 0.0) or 0.0) for _, m in legs)
        saved_cost_total = sum(float(m.get('cost', 0.0) or 0.0) for _, m in legs)
        shares_yes = sum(float(m.get('shares', 0.0) or 0.0) for _, m in legs if m.get('is_yes'))
        shares_no = sum(float(m.get('shares', 0.0) or 0.0) for _, m in legs if not m.get('is_yes'))
        yes_token = str(meta0.get('yes_token') or '')
        no_token = str(meta0.get('no_token') or '')
        held_yes = shares_yes >= shares_no
        held_side = 'UP' if held_yes else 'DN'
        redemption_kind = 'neg' if neg_risk else 'ctf'
        settlement_id = f'{(cond_id or market_id).lower()}:{redemption_kind}'

        def _official_from_winner(win_tid: str) -> Optional[Tuple[bool, float, bool]]:
            if not win_tid:
                return None
            if yes_token and win_tid == yes_token:
                up_won = True
            elif no_token and win_tid == no_token:
                up_won = False
            else:
                for _, meta in legs:
                    if str(meta.get('token_id') or '') == win_tid:
                        up_won = bool(meta.get('is_yes'))
                        break
                else:
                    return None
            proceeds = shares_yes if up_won else shares_no
            return (up_won if held_yes else not up_won, float(proceeds - saved_cost_total), up_won)

        def _official_from_spot() -> Optional[Tuple[bool, float, bool]]:
            # Paper settlement must use Chainlink price AT interval close â€” never live spot hours later.
            open_spot = float(meta0.get('open_price', 0.0) or 0.0)
            if open_spot <= 0 and market_id in self._open_prices:
                open_spot = float(self._open_prices.get(market_id) or 0.0)
            mkt_for_close = self._market_lookup(market_id) if self._market_lookup is not None else None
            end_ts = float(mkt_for_close.end_time or 0.0) if mkt_for_close is not None else 0.0
            if end_ts <= 0.0:
                try:
                    end_ts = float(meta0.get('end_time') or 0.0)
                except (TypeError, ValueError):
                    end_ts = 0.0
            if end_ts <= 0.0 or not self.tracker:
                return None
            final_spot = self.tracker.get_price_at(coin, end_ts, max_gap_s=10.0)
            if not final_spot or open_spot <= 0:
                return None
            up_won = final_spot > open_spot
            proceeds = shares_yes if up_won else shares_no
            return (up_won if held_yes else not up_won, float(proceeds - saved_cost_total), up_won)

        def _apply_settlement(proceeds: float, redeemed_amounts: List[float], source: str) -> None:
            existing_ledger = self._settlement_ledger.get(settlement_id)
            if existing_ledger and existing_ledger.get('phase') == 'booked':
                # A prior callback durably booked this settlement.  Returning lets
                # the engine retire its confirmed item without touching Risk again.
                self._notify_state()
                return
            if not math.isfinite(proceeds) or proceeds < 0.0:
                raise RuntimeStateError(f'settlement {settlement_id} has invalid authoritative payout {proceeds!r}')
            if len(redeemed_amounts) != 2 or any((not math.isfinite(float(x)) or float(x) < 0.0) for x in redeemed_amounts):
                raise RuntimeStateError(f'settlement {settlement_id} has invalid authoritative amounts {redeemed_amounts!r}')
            mkt = self._market_lookup(market_id) if self._market_lookup is not None else None
            if mkt is None:
                raise RuntimeStateError(f'settlement {settlement_id} cannot find canonical market inventory')
            local_amounts = [float(mkt.pos_yes.shares), float(mkt.pos_no.shares)]
            tolerance = max(1e-06, float(self.cfg.drift_halt_threshold_shares))
            if any(abs(local_amounts[i] - float(redeemed_amounts[i])) >= tolerance for i in range(2)):
                raise RuntimeStateError(f'settlement {settlement_id} receipt/local amount mismatch receipt={redeemed_amounts!r} local={local_amounts!r}')
            old_yes_cost = float(mkt.pos_yes.cost)
            old_no_cost = float(mkt.pos_no.cost)
            local_cost = old_yes_cost + old_no_cost
            if abs(local_cost - saved_cost_total) > max(0.01, tolerance):
                raise RuntimeStateError(f'settlement {settlement_id} metadata/local cost mismatch metadata={saved_cost_total:.6f} local={local_cost:.6f}')
            partial_pnl = 0.0
            partials = self._trade_pnl_in_flight_ref
            if partials is not None:
                for key in list(partials):
                    if key[0] == market_id:
                        partial_pnl += float(partials.pop(key, 0.0))
            soft_booked = any(bool((self._redeem_meta.get(key) or {}).get('risk_soft_booked')) for key in leg_keys)
            total_realized = float(proceeds) - local_cost + partial_pnl
            correction = total_realized if strategy == 'latarb' and not soft_booked else total_realized - est_total

            # Retire all account inventory and every strategy ownership marker
            # before writing the single durable booked ledger phase.
            mkt.pos_yes.shares = mkt.pos_yes.cost = 0.0
            mkt.pos_no.shares = mkt.pos_no.cost = 0.0
            mkt.latarb_hold_tokens.clear()
            mkt.latarb_hold = False
            for key in list(self._redeem_meta):
                if key[0] == market_id:
                    self._redeem_meta.pop(key, None)
            for mapping in (self._pending_redemptions, self._pending_entry, self._shares_in_flight, self._tp1_taken, self._entry_edges, self._raw_entry_px, self._fast_exit_counts, self._calib_entry_meta):
                for key in list(mapping):
                    if isinstance(key, tuple) and key and key[0] == market_id:
                        mapping.pop(key, None)
            self._traded.discard(market_id)
            self._open_prices.pop(market_id, None)
            self._entry_times.pop(market_id, None)
            self._realized_loss.pop(market_id, None)
            if self.om is not None:
                self.om.clear_entry_strategy(mkt.yes_token)
                self.om.clear_entry_strategy(mkt.no_token)
            self._net_exposure -= old_yes_cost - old_no_cost
            self._gross_exposure -= local_cost
            if abs(self._net_exposure) < 1e-09:
                self._net_exposure = 0.0
            self._gross_exposure = max(0.0, self._gross_exposure)
            self.risk.record_pnl(correction)
            self.risk.record_trade_closed(total_realized)
            if self._balance_ts > 0:
                self._balance_force_refresh = True
            self._settlement_ledger[settlement_id] = {
                'phase': 'booked', 'market_id': market_id, 'condition_id': cond_id,
                'kind': redemption_kind, 'source': source, 'payout': float(proceeds),
                'amounts': [float(redeemed_amounts[0]), float(redeemed_amounts[1])],
                'cost': local_cost, 'partial_pnl': partial_pnl,
                'realized': total_realized, 'correction': correction,
                'booked_at': time.time(), 'outcome_logged': True,
            }
            # This atomic snapshot is the accounting commit point.  If it fails,
            # the engine retains the confirmed item and retries this callback.
            self._notify_state()
            self.record_outcome(total_realized > 0.0, market_id=market_id, net_pnl=total_realized, coin=coin, side=held_side, strategy=strategy, outcome_kind='final')
            self.log.info('SETTLED %s | source=%s payout=$%.6f cost=$%.6f partial=$%+.6f realized=$%+.6f correction=$%+.6f', coin, source, proceeds, local_cost, partial_pnl, total_realized, correction)

        redeem_on = bool(self.redeemer and self.cfg.redeem_enabled and not self.cfg.dry_run)
        official = _official_from_winner(str(winning_asset_id or ''))
        if official is None and self.cfg.dry_run:
            official = _official_from_spot()

        if self.cfg.dry_run:
            if official is None:
                self.log.info('RESOLVED %s | dry-run lacks winner evidence; settlement retained', coin)
                self._notify_state()
                return
            _, _, up_won = official
            paper_payout = shares_yes if up_won else shares_no
            _apply_settlement(float(paper_payout), [shares_yes, shares_no], 'dry-oracle-close')
            return

        if not redeem_on:
            # Never book a live official estimate while retaining redeem metadata;
            # that old behavior could book again after redemption was re-enabled.
            self.log.warning('RESOLVED %s | live redemption disabled; no PnL booked and CTF metadata retained', coin)
            self._notify_state()
            return

        def _on_settled(proceeds: Optional[float], amounts: Optional[List[float]]) -> None:
            if proceeds is None or amounts is None:
                raise RuntimeStateError(f'settlement {settlement_id} missing authoritative receipt values')
            _apply_settlement(float(proceeds), [float(x) for x in amounts], 'adapter-event')

        enqueued = self.redeemer.enqueue(cond_id, neg_risk, shares_yes, shares_no, _on_settled)
        if not enqueued:
            self.log.debug('Redeem already queued/done for %s (%s)', cond_id[:18], redemption_kind)

def _latarb_fills_path(cfg: Optional['Config']=None) -> str:
    if cfg is not None and getattr(cfg, 'latarb_fills_path', None):
        return os.path.expanduser(cfg.latarb_fills_path)
    return os.path.expanduser(LATARB_FILLS_PATH)

def _latarb_settle_path(cfg: Optional['Config']=None) -> str:
    if cfg is not None and getattr(cfg, 'latarb_settle_path', None):
        return os.path.expanduser(cfg.latarb_settle_path)
    return os.path.expanduser(LATARB_SETTLE_PATH)

def _append_latarb_settle(row: dict, cfg: Optional['Config']=None) -> None:
    """Append one settlement-true LatArb outcome (jsonl). Best-effort."""
    try:
        path = _latarb_settle_path(cfg)
        os.makedirs(os.path.dirname(path) or '.', exist_ok=True)
        with open(path, 'a', encoding='utf-8') as fh:
            fh.write(json.dumps(row, separators=(',', ':')) + '\n')
    except Exception:
        pass

def _load_latarb_fills_stats(path: Optional[str]=None) -> dict:
    """Live proof prefers notional fill ratio = mean(fill_fraction) when logged."""
    p = os.path.expanduser(path or _latarb_fills_path())
    attempts = fills = 0
    if not os.path.exists(p):
        return {'attempts': 0, 'fills': 0, 'misses': 0, 'fill_rate': 0.0, 'live_attempts': 0, 'live_fills': 0, 'live_fill_rate': 0.0, 'live_notional_fill_ratio': 0.0}
    live_a = live_f = 0
    live_frac_sum = 0.0
    try:
        with open(p, encoding='utf-8') as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                try:
                    r = json.loads(line)
                except json.JSONDecodeError:
                    continue
                attempts += 1
                filled = bool(r.get('filled'))
                if filled:
                    fills += 1
                if not bool(r.get('dry_run', True)):
                    live_a += 1
                    if filled:
                        live_f += 1
                    try:
                        ff = float(r.get('fill_fraction') or 0.0)
                    except Exception:
                        ff = 1.0 if filled else 0.0
                    live_frac_sum += max(0.0, min(1.0, ff)) if filled or ff > 0 else 0.0
                    if not filled and ff <= 0:
                        pass
                    elif not filled:
                        live_frac_sum += 0.0
    except OSError:
        pass
    # Prefer sum(fill_fraction)/attempts (partial fills) over binary rate for live proof.
    live_ratio = live_frac_sum / live_a if live_a else 0.0
    if live_a and live_ratio <= 0 and live_f > 0:
        live_ratio = live_f / live_a
    return {'attempts': attempts, 'fills': fills, 'misses': max(0, attempts - fills), 'fill_rate': fills / attempts if attempts else 0.0, 'live_attempts': live_a, 'live_fills': live_f, 'live_fill_rate': live_f / live_a if live_a else 0.0, 'live_notional_fill_ratio': live_ratio}

def _load_latarb_settle_stats(cfg: Optional['Config']=None) -> dict:
    p = _latarb_settle_path(cfg)
    n = w = 0
    pnl = 0.0
    live_n = live_w = 0
    live_pnl = 0.0
    if not os.path.exists(p):
        return {'n': 0, 'wins': 0, 'win_rate': 0.0, 'pnl': 0.0, 'live_n': 0, 'live_wins': 0, 'live_win_rate': 0.0, 'live_pnl': 0.0}
    try:
        with open(p, encoding='utf-8') as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                try:
                    r = json.loads(line)
                except json.JSONDecodeError:
                    continue
                n += 1
                won = bool(r.get('win'))
                if won:
                    w += 1
                try:
                    pnl += float(r.get('net_pnl') or 0.0)
                except (TypeError, ValueError):
                    pass
                if not bool(r.get('dry_run', True)):
                    live_n += 1
                    if won:
                        live_w += 1
                    try:
                        live_pnl += float(r.get('net_pnl') or 0.0)
                    except (TypeError, ValueError):
                        pass
    except OSError:
        pass
    return {'n': n, 'wins': w, 'win_rate': w / n if n else 0.0, 'pnl': pnl, 'live_n': live_n, 'live_wins': live_w, 'live_win_rate': live_w / live_n if live_n else 0.0, 'live_pnl': live_pnl}

class RuntimeStateError(RuntimeError):
    pass

_LATARB_STATE_VERSION = 3
_LATARB_STATE_LOCK = threading.RLock()


def _runtime_state_identity(holder: str, chain_id: int, dry_run: bool) -> dict:
    clean_holder = str(holder or '').strip().lower()
    if not clean_holder:
        clean_holder = 'paper' if dry_run else ''
    if not clean_holder:
        raise RuntimeStateError('live runtime state requires a non-empty trading holder identity')
    return {'holder': clean_holder, 'chain_id': int(chain_id), 'mode': 'dry' if dry_run else 'live'}


def _latarb_state_path(identity: Optional[dict]=None) -> str:
    base = Path(os.path.expanduser(LATARB_STATE_PATH))
    if not identity:
        return str(base)
    holder = re.sub(r'[^a-zA-Z0-9_-]', '', str(identity.get('holder') or '').lower()) or 'unknown'
    chain_id = int(identity.get('chain_id') or 0)
    mode = str(identity.get('mode') or 'unknown')
    suffix = base.suffix or '.json'
    stem = base.stem if base.suffix else base.name
    return str(base.with_name(f'{stem}.{chain_id}.{mode}.{holder}{suffix}'))


def _finite_nonnegative(value: Any, label: str, upper: Optional[float]=None) -> float:
    try:
        number = float(value)
    except (TypeError, ValueError) as e:
        raise RuntimeStateError(f'{label} is not numeric') from e
    if not math.isfinite(number) or number < 0.0:
        raise RuntimeStateError(f'{label} must be finite and nonnegative, got {value!r}')
    if upper is not None and number > upper:
        raise RuntimeStateError(f'{label} exceeds safe bound {upper}: {number}')
    return number


def _validate_position_row(raw: Any, label: str) -> Tuple[float, float]:
    if not isinstance(raw, dict):
        raise RuntimeStateError(f'{label} must be an object')
    shares = _finite_nonnegative(raw.get('shares', 0.0), f'{label}.shares', 100_000_000.0)
    cost = _finite_nonnegative(raw.get('cost', 0.0), f'{label}.cost', 100_000_000.0)
    if shares <= 1e-09 and cost > 1e-09:
        raise RuntimeStateError(f'{label} has cost without shares')
    if shares > 1e-09 and cost <= 1e-09:
        raise RuntimeStateError(f'{label} has {shares:.6f} shares with zero cost basis')
    if shares > 1e-09 and cost > shares * 1.25 + 1e-06:
        raise RuntimeStateError(f'{label} cost/share {cost / shares:.6f} is economically invalid')
    return shares, cost


def _validate_runtime_state(state: dict, expected_identity: Optional[dict]=None) -> dict:
    if not isinstance(state, dict):
        raise RuntimeStateError('runtime state root must be an object')
    if state.get('version') != _LATARB_STATE_VERSION:
        raise RuntimeStateError(f'unsupported runtime state version {state.get("version")!r}; expected {_LATARB_STATE_VERSION}')
    identity = state.get('identity')
    if not isinstance(identity, dict):
        raise RuntimeStateError('runtime state identity is missing')
    normalized = _runtime_state_identity(identity.get('holder', ''), int(identity.get('chain_id') or 0), identity.get('mode') == 'dry')
    if str(identity.get('mode')) not in ('dry', 'live'):
        raise RuntimeStateError(f'invalid runtime state mode {identity.get("mode")!r}')
    normalized['mode'] = str(identity['mode'])
    if expected_identity is not None:
        expected = {'holder': str(expected_identity.get('holder') or '').lower(), 'chain_id': int(expected_identity.get('chain_id') or 0), 'mode': str(expected_identity.get('mode') or '')}
        if normalized != expected:
            raise RuntimeStateError(f'runtime state identity mismatch: saved={normalized!r} expected={expected!r}')
    saved_at = _finite_nonnegative(state.get('saved_at', 0.0), 'saved_at')
    if saved_at <= 0.0:
        raise RuntimeStateError('saved_at must be positive')
    markets = state.get('markets')
    if not isinstance(markets, dict):
        raise RuntimeStateError('markets must be an object')
    for mid, row in markets.items():
        if not str(mid) or not isinstance(row, dict):
            raise RuntimeStateError(f'invalid market row {mid!r}')
        if str(row.get('market_id') or '') != str(mid):
            raise RuntimeStateError(f'market row key/id mismatch for {mid!r}')
        _validate_position_row(row.get('pos_yes'), f'markets[{mid}].pos_yes')
        _validate_position_row(row.get('pos_no'), f'markets[{mid}].pos_no')
        holds = row.get('hold_tokens', [])
        if not isinstance(holds, list) or any(not isinstance(x, str) or not x for x in holds):
            raise RuntimeStateError(f'markets[{mid}].hold_tokens is invalid')
        if not str(row.get('yes_token') or '') or not str(row.get('no_token') or ''):
            raise RuntimeStateError(f'markets[{mid}] lacks outcome token identity')
    redeem_meta = state.get('redeem_meta', [])
    if not isinstance(redeem_meta, list):
        raise RuntimeStateError('redeem_meta must be an array')
    for i, entry in enumerate(redeem_meta):
        if not isinstance(entry, dict) or not isinstance(entry.get('meta'), dict):
            raise RuntimeStateError(f'redeem_meta[{i}] is invalid')
        meta = entry['meta']
        shares = _finite_nonnegative(meta.get('shares', 0.0), f'redeem_meta[{i}].shares', 100_000_000.0)
        cost = _finite_nonnegative(meta.get('cost', 0.0), f'redeem_meta[{i}].cost', 100_000_000.0)
        if shares > 1e-09 and cost <= 1e-09:
            raise RuntimeStateError(f'redeem_meta[{i}] has shares with zero cost basis')
        if shares > 1e-09 and cost > shares * 1.25 + 1e-06:
            raise RuntimeStateError(f'redeem_meta[{i}] has invalid cost/share')
    risk = state.get('risk', {})
    if not isinstance(risk, dict):
        raise RuntimeStateError('risk must be an object')
    for key in ('pnl', 'pnl_peak', 'day_start', 'day_age_s', 'month_start', 'month_age_s'):
        try:
            value = float(risk.get(key, 0.0))
        except (TypeError, ValueError) as e:
            raise RuntimeStateError(f'risk.{key} is not numeric') from e
        if not math.isfinite(value) or (key.endswith('_age_s') and value < 0.0):
            raise RuntimeStateError(f'risk.{key} is invalid: {value!r}')
    redemptions = state.get('redemptions', [])
    if not isinstance(redemptions, list):
        raise RuntimeStateError('redemptions must be an array')
    for i, item in enumerate(redemptions):
        if not isinstance(item, dict) or not str(item.get('condition_id') or ''):
            raise RuntimeStateError(f'redemptions[{i}] is invalid')
        for key in ('shares_yes', 'shares_no', 'receipt_payout'):
            if key in item:
                _finite_nonnegative(item[key], f'redemptions[{i}].{key}', 100_000_000.0)
        raw_hex, tx_hash = str(item.get('raw_tx') or ''), str(item.get('tx_hash') or '')
        if raw_hex:
            try:
                actual = Web3.to_hex(Web3.keccak(Web3.to_bytes(hexstr=raw_hex))).lower()
            except Exception as e:
                raise RuntimeStateError(f'redemptions[{i}].raw_tx is malformed') from e
            if not tx_hash or actual != tx_hash.lower():
                raise RuntimeStateError(f'redemptions[{i}] signed raw transaction/hash mismatch')
        phase = str(item.get('phase') or 'queued')
        if tx_hash and phase not in ('confirmed', 'receipt_error') and not raw_hex:
            raise RuntimeStateError(f'redemptions[{i}] has an unsafe hash-only pending transaction')
    partials = state.get('trade_pnl_in_flight', [])
    if not isinstance(partials, list):
        raise RuntimeStateError('trade_pnl_in_flight must be an array')
    for i, row in enumerate(partials):
        if not isinstance(row, dict) or not str(row.get('market_id') or '') or not str(row.get('token_id') or ''):
            raise RuntimeStateError(f'trade_pnl_in_flight[{i}] is invalid')
        try:
            pnl = float(row.get('pnl'))
        except (TypeError, ValueError) as e:
            raise RuntimeStateError(f'trade_pnl_in_flight[{i}].pnl is not numeric') from e
        if not math.isfinite(pnl):
            raise RuntimeStateError(f'trade_pnl_in_flight[{i}].pnl is not finite')
    if not isinstance(state.get('settlement_ledger', {}), dict):
        raise RuntimeStateError('settlement_ledger must be an object')
    if not isinstance(state.get('entry_strategies', {}), dict):
        raise RuntimeStateError('entry_strategies must be an object')
    if not isinstance(state.get('fill_apply_error', ''), str):
        raise RuntimeStateError('fill_apply_error must be a string')
    for key in ('applied_trade_ids', 'applied_ioc_order_ids'):
        values = state.get(key, [])
        if not isinstance(values, list) or len(values) > 10000 or any(not isinstance(x, str) or not x for x in values):
            raise RuntimeStateError(f'{key} must be an array of at most 10000 non-empty strings')
    return state


def _legacy_state_blocks_identity_path(path: str) -> bool:
    legacy = Path(os.path.expanduser(LATARB_STATE_PATH))
    candidate = Path(path)
    if candidate == legacy or candidate.parent != legacy.parent:
        return False
    if not candidate.name.startswith(legacy.stem + '.'):
        return False
    try:
        return legacy.exists() and legacy.stat().st_size > 0
    except OSError:
        return False


def _load_latarb_state(path: Optional[str]=None, expected_identity: Optional[dict]=None, strict: bool=False) -> dict:
    selected = str(path or _latarb_state_path(expected_identity))
    if not os.path.exists(selected) or os.path.getsize(selected) == 0:
        if _legacy_state_blocks_identity_path(selected):
            msg = f'legacy unbound runtime state exists at {_latarb_state_path()}; move/reconcile it explicitly before using identity-bound state {selected}'
            if strict:
                raise RuntimeStateError(msg)
            logging.getLogger('Bot').warning(msg)
        return {}
    try:
        with open(selected, 'r', encoding='utf-8') as fh:
            raw = json.load(fh)
        return _validate_runtime_state(raw, expected_identity)
    except Exception as e:
        if strict:
            if isinstance(e, RuntimeStateError):
                raise
            raise RuntimeStateError(f'runtime state load failed for {selected}: {e}') from e
        logging.getLogger('Bot').warning('Ignoring unusable runtime state %s: %s', selected, e)
        return {}


def _write_latarb_state_unlocked(state: dict, path: str) -> None:
    os.makedirs(os.path.dirname(path) or '.', exist_ok=True)
    tmp = f'{path}.{os.getpid()}.{threading.get_ident()}.tmp'
    try:
        with open(tmp, 'w', encoding='utf-8') as fh:
            json.dump(state, fh, separators=(',', ':'), allow_nan=False)
            fh.flush()
            os.fsync(fh.fileno())
        os.replace(tmp, path)
    finally:
        try:
            if os.path.exists(tmp):
                os.unlink(tmp)
        except OSError:
            pass


def _save_latarb_state(state: dict, path: Optional[str]=None, expected_identity: Optional[dict]=None) -> None:
    selected = str(path or _latarb_state_path(expected_identity or state.get('identity')))
    _validate_runtime_state(state, expected_identity)
    with _LATARB_STATE_LOCK:
        _write_latarb_state_unlocked(state, selected)


def _market_runtime_row(mkt: 'Market') -> dict:
    return {
        'market_id': str(mkt.market_id), 'question': str(mkt.question or ''),
        'yes_token': str(mkt.yes_token), 'no_token': str(mkt.no_token),
        'condition_id': str(getattr(mkt, 'condition_id', '') or ''),
        'end_time': float(mkt.end_time) if mkt.end_time else None,
        'coin': str(mkt.coin or ''), 'tf_secs': int(mkt.tf_secs),
        'neg_risk': bool(mkt.neg_risk),
        'hold_tokens': sorted(getattr(mkt, 'latarb_hold_tokens', set()) or set()),
        'pos_yes': {'shares': float(mkt.pos_yes.shares), 'cost': float(mkt.pos_yes.cost)},
        'pos_no': {'shares': float(mkt.pos_no.shares), 'cost': float(mkt.pos_no.cost)},
    }


def _snapshot_runtime_state(markets: List['Market'], strategy: Optional['FiveMinStrategy'], risk: Optional['Risk'], redeemer: Optional['RedemptionEngine'], dry_run: bool, identity: dict, path: str, trade_pnl_in_flight: Optional[Dict[Tuple[str, str], float]]=None, om: Optional['OrderManager']=None, applied_trade_ids: Optional[Deque[str]]=None, applied_ioc_order_ids: Optional[Deque[str]]=None) -> dict:
    with _LATARB_STATE_LOCK:
        market_rows: Dict[str, dict] = {}
        meta_mids: Set[str] = set()
        redeem_rows: List[dict] = []
        settlement_ledger: Dict[str, dict] = {}
        if strategy is not None:
            for (mid, token), meta in list(strategy._redeem_meta.items()):
                meta_mids.add(str(mid))
                redeem_rows.append({'market_id': str(mid), 'token_id': str(token), 'meta': dict(meta)})
            settlement_ledger = {str(k): dict(v) for k, v in getattr(strategy, '_settlement_ledger', {}).items()}
        for mkt in list(markets):
            if mkt.pos_yes.shares > 1e-09 or mkt.pos_no.shares > 1e-09 or getattr(mkt, 'latarb_hold_tokens', set()) or str(mkt.market_id) in meta_mids:
                market_rows[str(mkt.market_id)] = _market_runtime_row(mkt)
        risk_row: dict = {}
        if risk is not None:
            risk_row = {'pnl': float(risk._pnl), 'pnl_peak': float(risk._pnl_peak), 'day_start': float(risk._day_start), 'day_age_s': max(0.0, time.monotonic() - risk._day_reset), 'month_start': float(risk._month_start), 'month_age_s': max(0.0, time.monotonic() - risk._month_reset), 'consecutive_losses': int(risk._consecutive_losses), 'halted': bool(risk._halted), 'halt_type': str(risk._halt_type), 'reason': str(risk._reason)}
        redemption_rows: List[dict] = []
        done_rows: List[List[str]] = []
        if redeemer is not None:
            for item in list(redeemer._items.values()):
                redemption_rows.append({k: item[k] for k in redeemer._PERSIST_FIELDS if k in item})
            done_rows = [[str(cid), str(kind)] for cid, kind in sorted(redeemer._done)]
        partial_rows = [{'market_id': str(mid), 'token_id': str(token), 'pnl': float(pnl)} for (mid, token), pnl in sorted((trade_pnl_in_flight or {}).items())]
        entry_strategies = dict(getattr(om, '_entry_strategy_by_token', {})) if om is not None else {}
        state = {'version': _LATARB_STATE_VERSION, 'identity': dict(identity), 'saved_at': time.time(), 'markets': market_rows, 'redeem_meta': redeem_rows, 'settlement_ledger': settlement_ledger, 'risk': risk_row, 'redemptions': redemption_rows, 'done_redemptions': done_rows, 'trade_pnl_in_flight': partial_rows, 'entry_strategies': entry_strategies, 'applied_trade_ids': list(applied_trade_ids or ()), 'applied_ioc_order_ids': list(applied_ioc_order_ids or ()), 'fill_apply_error': str(getattr(om, '_fill_apply_error', '') or '') if om is not None else ''}
        _validate_runtime_state(state, identity)
        _write_latarb_state_unlocked(state, path)
        return state


def _apply_latarb_state_to_markets(markets: List['Market'], state: dict, om: Optional['OrderManager']=None) -> int:
    rows = state.get('markets', {})
    by_id = {str(m.market_id): m for m in markets}
    n = 0
    for mid, row in rows.items():
        mkt = by_id.get(str(mid))
        if mkt is None:
            continue
        if str(mkt.yes_token) != str(row.get('yes_token')) or str(mkt.no_token) != str(row.get('no_token')):
            raise RuntimeStateError(f'persisted outcome-token identity changed for market {mid}')
        toks = [str(t) for t in row.get('hold_tokens', []) if t]
        mkt.latarb_hold_tokens = set(toks)
        for key, pos in (('pos_yes', mkt.pos_yes), ('pos_no', mkt.pos_no)):
            shares, cost = _validate_position_row(row.get(key), f'markets[{mid}].{key}')
            pos.shares, pos.cost = shares, cost
        mkt.latarb_hold = bool(toks)
        if toks or mkt.pos_yes.shares > 1e-09 or mkt.pos_no.shares > 1e-09:
            n += 1
    if om is not None:
        om._entry_strategy_by_token = {str(k): str(v) for k, v in state.get('entry_strategies', {}).items() if v in ('latarb', 'directional')}
        for mkt in markets:
            for token in mkt.latarb_hold_tokens:
                om.tag_entry_strategy(token, 'latarb')
    return n


def _market_from_runtime_row(row: dict) -> 'Market':
    mkt = Market(market_id=str(row['market_id']), question=str(row.get('question') or '[persisted recovery placeholder]'), yes_token=str(row['yes_token']), no_token=str(row['no_token']), condition_id=str(row.get('condition_id') or ''), end_time=float(row['end_time']) if row.get('end_time') is not None else None, coin=str(row.get('coin') or '') or None, tf_secs=int(row.get('tf_secs') or 300), neg_risk=bool(row.get('neg_risk')))
    setattr(mkt, '_recovery_placeholder', True)
    return mkt


def _merge_persisted_market_placeholders(markets: List['Market'], state: dict) -> List['Market']:
    merged = list(markets)
    by_id = {str(m.market_id): m for m in merged}
    for mid, row in state.get('markets', {}).items():
        existing = by_id.get(str(mid))
        if existing is None:
            placeholder = _market_from_runtime_row(row)
            merged.append(placeholder)
            by_id[str(mid)] = placeholder
        elif str(existing.yes_token) != str(row.get('yes_token')) or str(existing.no_token) != str(row.get('no_token')):
            raise RuntimeStateError(f'discovered outcome-token identity differs from persisted state for market {mid}')
    return merged


def _restore_runtime_state(markets: List['Market'], strategy: 'FiveMinStrategy', risk: 'Risk', redeemer: 'RedemptionEngine', om: 'OrderManager', dry_run: bool, state: Optional[dict]=None, trade_pnl_in_flight: Optional[Dict[Tuple[str, str], float]]=None, applied_trade_ids: Optional[Deque[str]]=None, applied_ioc_order_ids: Optional[Deque[str]]=None) -> Tuple[int, Set[str], List[str]]:
    state = state or {}
    if not state:
        return (0, set(), [])
    n = _apply_latarb_state_to_markets(markets, state, om)
    om._fill_apply_error = str(state.get('fill_apply_error') or '')
    restored_mids: Set[str] = set()
    for row in state.get('redeem_meta', []):
        mid, token, meta = str(row.get('market_id') or ''), str(row.get('token_id') or ''), row.get('meta')
        if not mid or not token or not isinstance(meta, dict):
            continue
        key = (mid, token)
        clean = dict(meta)
        strategy._redeem_meta[key] = clean
        shares = float(clean.get('shares', 0.0) or 0.0)
        cost = float(clean.get('cost', 0.0) or 0.0)
        strategy._pending_redemptions[key] = (shares, cost / shares if shares > 1e-09 else 0.0, 1.0)
        if clean.get('open_price'):
            strategy._open_prices[mid] = float(clean['open_price'])
        restored_mids.add(mid)
    strategy._settlement_ledger = {str(k): dict(v) for k, v in state.get('settlement_ledger', {}).items() if isinstance(v, dict)}
    strategy._net_exposure = 0.0
    strategy._gross_exposure = 0.0
    for mkt in markets:
        if mkt.pos_yes.shares > 1e-09 or mkt.pos_no.shares > 1e-09:
            strategy._traded.add(mkt.market_id)
        strategy._net_exposure += mkt.pos_yes.cost - mkt.pos_no.cost
        strategy._gross_exposure += mkt.pos_yes.cost + mkt.pos_no.cost
    saved_at = float(state.get('saved_at', time.time()))
    downtime = max(0.0, time.time() - saved_at)
    rr = state.get('risk') or {}
    if rr:
        risk._pnl = float(rr.get('pnl', 0.0))
        risk._pnl_peak = max(risk._pnl, float(rr.get('pnl_peak', risk._pnl)))
        day_age = max(0.0, float(rr.get('day_age_s', 0.0)) + downtime)
        month_age = max(0.0, float(rr.get('month_age_s', 0.0)) + downtime)
        risk._day_start = risk._pnl if day_age >= 86400.0 else float(rr.get('day_start', risk._pnl))
        risk._day_reset = time.monotonic() if day_age >= 86400.0 else time.monotonic() - day_age
        risk._month_start = risk._pnl if month_age >= 30 * 86400.0 else float(rr.get('month_start', risk._pnl))
        risk._month_reset = time.monotonic() if month_age >= 30 * 86400.0 else time.monotonic() - month_age
        risk._consecutive_losses = 0 if day_age >= 86400.0 else int(rr.get('consecutive_losses', 0))
        halt_type = str(rr.get('halt_type') or '')
        keep_halt = bool(rr.get('halted')) and not (day_age >= 86400.0 and halt_type in ('daily_loss', 'consec_losses'))
        risk._halted, risk._halt_type, risk._reason = keep_halt, halt_type if keep_halt else '', str(rr.get('reason') or '') if keep_halt else ''
    if trade_pnl_in_flight is not None:
        trade_pnl_in_flight.clear()
        for row in state.get('trade_pnl_in_flight', []):
            trade_pnl_in_flight[(str(row['market_id']), str(row['token_id']))] = float(row['pnl'])
    if applied_trade_ids is not None:
        applied_trade_ids.clear()
        applied_trade_ids.extend(str(x) for x in state.get('applied_trade_ids', []))
    if applied_ioc_order_ids is not None:
        applied_ioc_order_ids.clear()
        applied_ioc_order_ids.extend(str(x) for x in state.get('applied_ioc_order_ids', []))
    redeemer._done = {(str(x[0]), str(x[1])) for x in state.get('done_redemptions', []) if isinstance(x, list) and len(x) == 2}
    for item in state.get('redemptions', []):
        kind = 'neg' if bool(item.get('neg_risk')) else 'ctf'
        key = (str(item['condition_id']), kind)
        ledger_id = f'{str(item["condition_id"]).lower()}:{kind}'
        if (strategy._settlement_ledger.get(ledger_id) or {}).get('phase') == 'booked':
            redeemer._done.add(key)
            continue
        redeemer._resume_items[key] = dict(item)
    problems: List[str] = []
    meta_keys = {(str(v.get('condition_id') or ''), str(v.get('token_id') or '')) for v in strategy._redeem_meta.values()}
    for mid, row in state.get('markets', {}).items():
        for pkey, token_key in (('pos_yes', 'yes_token'), ('pos_no', 'no_token')):
            shares = float((row.get(pkey) or {}).get('shares', 0.0) or 0.0)
            marker = (str(row.get('condition_id') or ''), str(row.get(token_key) or ''))
            if shares > 1e-09 and marker not in meta_keys:
                problems.append(f'persisted orphan position {mid}/{token_key} has {shares:.6f} shares but no settlement metadata')
    return (n, restored_mids, problems)

def _fok_sweep_price(book: Optional[OrderBook], size_usdc: float, tick: float, dec: int, mt: int) -> float:
    if not book or not book._asks_int:
        return 0.0
    PS = OrderBook.PRICE_SCALE
    SS = OrderBook.SIZE_SCALE
    rem_scaled = int(round(size_usdc * PS * SS))
    worst_key = 0
    for key in sorted(book._asks_int.keys()):
        if key <= 0:
            continue
        worst_key = key
        level_notional = key * book._asks_int[key]
        rem_scaled -= level_notional
        if rem_scaled <= 0:
            break
    if rem_scaled > 0:
        return 0.0
    worst_price = worst_key / PS
    return snap_price(worst_price + tick, tick, 'BUY', dec, mt)

def _fak_limit_and_size(book: Optional[OrderBook], size_usdc: float, model_prob: float, fee_rate: float, taker_delay: float, min_edge: float, tick: float, dec: int, mt: int, min_size: float) -> Tuple[float, float]:
    """Deepest ask level whose cumulative VWAP still clears min_edge; return (limit_px, size_usdc)."""
    if not book or not book._asks_int or size_usdc <= 0 or min_size <= 0:
        return (0.0, 0.0)
    PS = OrderBook.PRICE_SCALE
    SS = OrderBook.SIZE_SCALE
    target = int(round(size_usdc * PS * SS))
    cost_scaled = 0
    shares_int = 0
    worst_key = 0
    best_limit = 0.0
    best_sz = 0.0
    for key in sorted(book._asks_int.keys()):
        if key <= 0:
            continue
        level_size = book._asks_int[key]
        level_notional = key * level_size
        take_notional = min(level_notional, target - cost_scaled) if target > cost_scaled else 0
        if take_notional <= 0:
            break
        taken_shares = take_notional // key
        if taken_shares <= 0:
            break
        cost_scaled += taken_shares * key
        shares_int += taken_shares
        worst_key = key
        vwap = cost_scaled / shares_int / PS
        fee = fee_rate * vwap * (1.0 - vwap) if fee_rate > 0 else 0.0
        edge = model_prob - vwap - fee - taker_delay
        notional = cost_scaled / (PS * SS)
        if edge >= min_edge and notional + 1e-09 >= min_size:
            lim = snap_price(worst_key / PS, tick, 'BUY', dec, mt)
            best_limit = lim
            best_sz = round(min(size_usdc, notional), 2)
        if cost_scaled >= target:
            break
    return (best_limit, best_sz)

def _fok_sweep_price_sell(book: Optional[OrderBook], shares: float, tick: float, dec: int, mt: int) -> float:
    if not book or not book._bids_int:
        return 0.0
    PS = OrderBook.PRICE_SCALE
    SS = OrderBook.SIZE_SCALE
    rem_shares = int(round(shares * SS))
    if rem_shares <= 0:
        return 0.0
    worst_key = 0
    for key in sorted(book._bids_int.keys(), reverse=True):
        if key <= 0:
            continue
        worst_key = key
        rem_shares -= book._bids_int[key]
        if rem_shares <= 0:
            break
    if rem_shares > 0 or worst_key <= 0:
        return 0.0
    worst_price = worst_key / PS
    return snap_price(worst_price, tick, 'SELL', dec, mt)

def _latarb_fill_fraction(matched_shares: float, requested_shares: float) -> float:
    if not math.isfinite(matched_shares) or not math.isfinite(requested_shares) or requested_shares <= 0.0:
        return 0.0
    return max(0.0, min(1.0, matched_shares / requested_shares))

class LatencyArb:

    def __init__(self, cfg: Config, om: OrderManager, tracker: PriceTracker, polyfeed: HyperPolyFeed, by_coin: Dict[str, List[Market]]):
        self.cfg = cfg
        self.om = om
        self.tracker = tracker
        self.polyfeed = polyfeed
        self.by_coin = by_coin
        self.log = get_logger('LatencyArb', cfg.log_level)
        self._cooldowns: Dict[str, float] = {}
        self._shadow_last: Dict[str, float] = {}
        self._last_latarb_log: Dict[str, float] = {}
        self._shadow_fh = None
        self._shadow_init_done = False
        self._shadow_writes = 0
        # First executable shadow candidate per market (independent of throttle spam).
        self._shadow_candidate_logged: Set[str] = set()
        self._traded_entries: Set[str] = set()
        self._shadow_pool = concurrent.futures.ThreadPoolExecutor(max_workers=1, thread_name_prefix='latarb-shadow-io')
        self._measure_only = False
        self._measure_only_until: float = 0.0
        self.risk = None
        self.strategy = None
        # F1: live/dry FAK attempt accounting (fill rate is the binding unknown).
        self.attempts: int = 0
        self.fills: int = 0
        self.misses: int = 0
        self._edge_sum: float = 0.0
        self._slip_bps_sum: float = 0.0
        self._slip_n: int = 0
        self._expected_fill_px: Dict[str, float] = {}  # token â†’ submission-time expected VWAP
        self._recent_fill_flags: Deque[int] = deque(maxlen=LATARB_KILL_WINDOW)
        self._fill_log_pool = concurrent.futures.ThreadPoolExecutor(max_workers=1, thread_name_prefix='latarb-fill-io')
        # Live-proof sizing flag. Refreshed by Bot._boot and Bot._status_loop off
        # the event loop; _eval_market only reads it (was a blocking JSONL scan).
        self._live_proof_ok: bool = False
        self._inflight: Set[str] = set()
        self._place_lock = asyncio.Lock()
        self._skip_log_last: Dict[str, float] = {}
        self._skip_counts = Counter()

    def _note_latarb_skip(self, key: str) -> None:
        self._skip_counts[str(key)] += 1

    def _skip_latarb(self, key: str, msg: str='', *args: Any) -> None:
        if msg:
            self._log_latarb_skip(key, msg, *args)
        else:
            self._note_latarb_skip(key)
        return None

    def skip_summary(self, limit: int=8) -> str:
        if not self._skip_counts:
            return ''
        return ', '.join(f'{k}={v}' for k, v in self._skip_counts.most_common(max(1, int(limit))))

    def _log_latarb_skip(self, key: str, msg: str, *args: Any) -> None:
        """Throttle silent pre-fire returns so halt/bankroll are visible (not silent)."""
        self._note_latarb_skip(key)
        now = time.monotonic()
        if now - self._skip_log_last.get(key, 0.0) < 30.0:
            return
        self._skip_log_last[key] = now
        self.log.warning('LATARB_SKIP [%s] ' + msg, key, *args)

    def _taker_delay_seconds(self) -> float:
        """Signalâ†’fill horizon for delay buffer: measured order p95 when available, else 250ms."""
        p95_s = LATARB_DEFAULT_TAKER_DELAY_S
        metrics = getattr(self.om, '_metrics', None) if self.om is not None else None
        if metrics is not None:
            try:
                ms = float((metrics.summary() or {}).get('lat_p95_ms') or 0.0)
                if ms > 0.0:
                    p95_s = max(0.05, min(2.0, ms / 1000.0))
            except Exception:
                pass
        return p95_s

    def fills_summary(self) -> dict:
        a = self.attempts
        fr = self.fills / a if a else 0.0
        avg_edge = self._edge_sum / a if a else 0.0
        avg_slip = self._slip_bps_sum / self._slip_n if self._slip_n else 0.0
        rw = list(self._recent_fill_flags)
        rw_n = len(rw)
        rw_fr = (sum(rw) / rw_n) if rw_n else 0.0
        return {'attempts': a, 'fills': self.fills, 'misses': self.misses, 'fill_rate': fr, 'avg_edge': avg_edge, 'avg_slip_bps': avg_slip, 'rolling_n': rw_n, 'rolling_fill_rate': rw_fr}

    def maybe_update_kill_switch(self) -> None:
        """Rolling-window fill kill + auto re-enable after cooldown (not a one-way latch)."""
        if self.cfg.dry_run or not self.cfg.latency_arb_enabled:
            return
        now = time.time()
        rw = list(self._recent_fill_flags)
        n = len(rw)
        if self._measure_only:
            if now < self._measure_only_until:
                return
            if n >= LATARB_MIN_LIVE_ATTEMPTS_FOR_KILL:
                rw_fr = sum(rw) / n
                if rw_fr >= LATARB_KILL_SWITCH_MIN_FILL_RATE:
                    self._measure_only = False
                    self._measure_only_until = 0.0
                    self.log.info('LatArb re-enabled: rolling fill rate %.0f%% over last %d attempts recovered', 100.0 * rw_fr, n)
            return
        if n >= LATARB_MIN_LIVE_ATTEMPTS_FOR_KILL:
            rw_fr = sum(rw) / n
            if rw_fr < LATARB_KILL_SWITCH_MIN_FILL_RATE:
                self._measure_only = True
                self._measure_only_until = now + LATARB_KILL_COOLDOWN_S
                self.log.critical('LatArb measure-only: rolling fill rate %.0f%% over last %d FAK attempts < %.0f%% â€” pause %.0fs then re-check', 100.0 * rw_fr, n, 100.0 * LATARB_KILL_SWITCH_MIN_FILL_RATE, LATARB_KILL_COOLDOWN_S)

    def _record_fok_attempt(self, *, filled: bool, sweep: float, edge: float, coin: str, market_id: str, token: str, model_prob: float, expected_vwap: Optional[float]=None, matched_size: float=0.0, fill_fraction: float=0.0, actual_fill_px: float=0.0) -> None:
        self.attempts += 1
        self._edge_sum += float(edge)
        self._recent_fill_flags.append(1 if filled else 0)
        if filled:
            self.fills += 1
            if token:
                exp = float(expected_vwap) if expected_vwap and expected_vwap > 0 else float(sweep)
                self._expected_fill_px[token] = exp
        else:
            self.misses += 1
            self._expected_fill_px.pop(token, None)
        # fill_fraction already clamped in _latarb_fill_fraction; re-clamp for log safety.
        ff = max(0.0, min(1.0, float(fill_fraction))) if math.isfinite(float(fill_fraction)) else 0.0
        row = {'ts': time.time(), 'coin': coin, 'market_id': market_id, 'token': token[:16] if token else '', 'filled': bool(filled), 'matched_size': round(float(matched_size), 6), 'fill_fraction': round(ff, 6), 'sweep': round(float(sweep), 6), 'expected_vwap': round(float(expected_vwap or 0.0), 6), 'actual_fill_px': round(float(actual_fill_px or 0.0), 6), 'edge': round(float(edge), 6), 'model_prob': round(float(model_prob), 6), 'dry_run': bool(self.cfg.dry_run)}
        try:
            self._fill_log_pool.submit(self._append_fill_log, row)
        except RuntimeError:
            pass
        self.maybe_update_kill_switch()

    def record_realized_slip(self, token_id: str, fill_px: float) -> None:
        exp = self._expected_fill_px.pop(token_id, None)
        if exp is None or exp <= 0 or fill_px <= 0:
            return
        # Slippage vs submission-time expected VWAP (not the worst-price sweep limit).
        slip_bps = (float(fill_px) - float(exp)) / float(exp) * 10000.0
        self._slip_bps_sum += slip_bps
        self._slip_n += 1

    def _append_fill_log(self, row: dict) -> None:
        try:
            path = _latarb_fills_path(self.cfg)
            os.makedirs(os.path.dirname(path) or '.', exist_ok=True)
            with open(path, 'a', encoding='utf-8') as fh:
                fh.write(json.dumps(row, separators=(',', ':')) + '\n')
        except Exception:
            pass

    async def on_binance_tick(self, coin: str, price: float, *, is_lead: bool=True) -> None:
        # Lead signal = Binance (is_lead=True). Oracle wake (is_lead=False) reuses last Binance px.
        # Settlement open still from Chainlink history; CL confirms sign when fresh.
        raw_px = float(price) if price and price > 0 else 0.0
        if raw_px <= 0:
            return
        if is_lead and self.tracker is not None:
            try:
                await self.tracker.ingest_lead_tick(coin, raw_px)
            except Exception:
                pass
        if is_lead:
            lead_px = raw_px
        else:
            # Oracle-driven wake: reuse Binance only while it is fresh; otherwise
            # fall back to the current oracle tick instead of stale lead displacement.
            prev = self.tracker._lead_last.get(coin) if self.tracker is not None else None
            prev_age_s = time.time() - float(prev[0]) if prev else float('inf')
            lead_px = float(prev[1]) if prev and prev[1] > 0 and 0.0 <= prev_age_s <= 2.0 else raw_px
        if lead_px <= 0:
            return
        oracle_px = None
        if self.tracker is not None and self.tracker.feed is not None:
            try:
                oracle_px = self.tracker.feed.price(coin, max_age_s=2.0)
            except Exception:
                oracle_px = None
        if not is_lead and raw_px > 0:
            oracle_px = raw_px
        if self.cfg.latarb_shadow:
            # Shadow records the LEADING path (same as live fire) so analyze = latency thesis.
            self._shadow_scan(coin, lead_px, oracle_px=oracle_px)
        if not self.cfg.latency_arb_enabled:
            return
        if self._measure_only and (not self.cfg.dry_run):
            return
        if self.risk is not None and (not self.risk.ok()):
            st = self.risk.status()
            self._log_latarb_skip('risk_halt', 'type=%s reason=%s consec=%s day=$%.2f', st.get('halt_type', ''), st.get('reason', ''), st.get('consec_losses', 0), st.get('daily', 0.0))
            return
        strat0 = self.strategy
        if strat0 is not None and (not self.cfg.dry_run) and getattr(strat0, 'in_capital_shock_cooldown', lambda: False)():
            return self._skip_latarb('capital_shock')
        _bankroll_ref = getattr(self.risk, '_bankroll_ref', None) if self.risk is not None else None
        if _bankroll_ref is not None:
            try:
                _bankroll = max(0.0, float(_bankroll_ref() or 0.0))
            except Exception:
                _bankroll = 0.0
        else:
            _bankroll = 0.0
        if not self.cfg.dry_run:
            if _bankroll_ref is None:
                self._log_latarb_skip('bankroll', 'no bankroll_ref (live)')
                return
            if _bankroll <= 0.0:
                self._log_latarb_skip('bankroll', 'bankroll=$%.4f <= 0', _bankroll)
                return
            if self.cfg.min_order_size > _bankroll * self.cfg.max_bankroll_fraction:
                self._log_latarb_skip('bankroll', 'min_order $%.2f > bankroll $%.4f * frac %.2f', self.cfg.min_order_size, _bankroll, self.cfg.max_bankroll_fraction)
                return
        elif _bankroll > 0.0 and self.cfg.min_order_size > _bankroll * self.cfg.max_bankroll_fraction:
            self._log_latarb_skip('bankroll', 'dry sizing inert: min_order $%.2f > bankroll $%.4f * frac %.2f', self.cfg.min_order_size, _bankroll, self.cfg.max_bankroll_fraction)
            return
        self._cleanup_counter = getattr(self, '_cleanup_counter', 0) + 1
        if self._cleanup_counter % 100 == 0:
            _cleanup_now = time.time()
            self._cooldowns = {k: v for k, v in self._cooldowns.items() if v > _cleanup_now}
            _cleanup_mono = time.monotonic()
            self._last_latarb_log = {k: v for k, v in self._last_latarb_log.items() if _cleanup_mono - v <= 60.0}
        markets = list(self.by_coin.get(coin, []))
        if not markets:
            return
        results = await asyncio.gather(*(self._eval_market(mkt, coin, lead_px, _bankroll, oracle_px=oracle_px) for mkt in markets), return_exceptions=True)
        for mkt, result in zip(markets, results):
            if isinstance(result, Exception):
                self._log_latarb_skip(f'eval_error:{mkt.market_id}', 'eval error %s %s: %s', coin, mkt.market_id, result)

    async def _eval_market(self, mkt: Market, coin: str, price: float, _bankroll: float, oracle_px: Optional[float]=None) -> None:
        now = time.time()
        if not mkt.end_time or not mkt.coin:
            return
        ttc = mkt.end_time - now
        if ttc < 30 or ttc > mkt.tf_secs - 15:
            self._traded_entries.discard(mkt.market_id)
            if ttc < 0:
                self._shadow_candidate_logged.discard(mkt.market_id)
            strat = self.strategy
            if strat is not None:
                strat._traded.discard(mkt.market_id)
                strat._pending_entry.pop((mkt.market_id, mkt.yes_token), None)
                strat._pending_entry.pop((mkt.market_id, mkt.no_token), None)
            return
        if now < self._cooldowns.get(mkt.market_id, 0):
            return self._skip_latarb('cooldown')
        if mkt.market_id in self._traded_entries and mkt.pos_yes.shares < 1e-06 and (mkt.pos_no.shares < 1e-06) and (not self.om.find_open(mkt.yes_token, Side.BUY)) and (not self.om.find_open(mkt.no_token, Side.BUY)):
            strat = self.strategy
            if strat is not None:
                strat._pending_entry.pop((mkt.market_id, mkt.yes_token), None)
                strat._pending_entry.pop((mkt.market_id, mkt.no_token), None)
            if not getattr(mkt, 'latarb_hold_tokens', set()):
                self._traded_entries.discard(mkt.market_id)
                mkt.latarb_hold = False
                if strat is not None:
                    strat._traded.discard(mkt.market_id)
        interval_start = mkt.start_time
        if not interval_start:
            return self._skip_latarb('missing_interval_start')
        # Open from settlement-oracle history (Chainlink). Lead price = Binance for displacement.
        open_price = self.tracker.get_price_at_or_before(coin, interval_start, max_lag_s=10.0)
        if not open_price or open_price <= 0:
            return self._skip_latarb('missing_open_price')
        # Persist open price for settle meta (LatArb owns this now).
        strat_op = self.strategy
        if strat_op is not None and mkt.market_id not in strat_op._open_prices:
            strat_op._open_prices[mkt.market_id] = float(open_price)
        displacement = (price - open_price) / open_price
        up = displacement > 0
        # Settlement-oracle sign agreement when fresh CL is available (basis filter).
        if oracle_px is not None and oracle_px > 0 and open_price > 0:
            o_disp = (float(oracle_px) - open_price) / open_price
            if o_disp * displacement < 0.0:
                return self._skip_latarb('oracle_sign', '%s %s oracle sign disagrees lead: lead_disp=%+.5f oracle_disp=%+.5f', coin, mkt.market_id, displacement, o_disp)
        else:
            # N12 FIX: oracle feed stale/missing â€” cannot confirm displacement direction
            return self._skip_latarb('oracle_stale', '%s %s oracle feed stale/missing (oracle_px=None)', coin, mkt.market_id)
        book = mkt.book_yes if up else mkt.book_no
        token_chk = mkt.yes_token if up else mkt.no_token
        # P0: no LatArb on reconnect / missing snapshot / crossed book
        if self.polyfeed is not None and (not self.polyfeed.book_ready(token_chk)):
            return self._skip_latarb('book_not_ready')
        if mkt.book_yes is not None and self.polyfeed is not None and (not self.polyfeed.book_ready(mkt.yes_token)):
            return self._skip_latarb('yes_book_not_ready')
        if mkt.book_no is not None and self.polyfeed is not None and (not self.polyfeed.book_ready(mkt.no_token)):
            return self._skip_latarb('no_book_not_ready')
        # Transport age (last WS touch). No hard 600ms floor â€” liquid books never clear it.
        min_age = max(0.0, float(self.cfg.latarb_shadow_min_age_ms))
        if not book or book.age_ms < min_age:
            return self._skip_latarb('book_too_fresh')
        if self.cfg.latarb_shadow_max_age_ms > 0.0 and book.age_ms > self.cfg.latarb_shadow_max_age_ms:
            return self._skip_latarb('book_stale')
        if mkt.book_yes is not None and mkt.book_no is not None and (min(mkt.book_yes.age_ms, mkt.book_no.age_ms) > LATARB_DUAL_BOOK_STALE_MS):
            return self._skip_latarb('dual_book_stale')
        if book.is_crossed:
            return self._skip_latarb('crossed_book')
        # D1 FIX: enforce max_spread_pct in LatArb path (was missing; directional has it at 4121)
        if book.spread_pct > self.cfg.max_spread_pct:
            return self._skip_latarb('spread_too_wide', '%s %s spread %.4f > max %.4f', coin, mkt.market_id, book.spread_pct, self.cfg.max_spread_pct)
        ask = book.best_ask
        if ask is None or ask > 0.65:
            return self._skip_latarb('ask_cap')
        sigma_per_sec = max(self.tracker.volatility(coin), GBM_SIGMA_FLOOR_PER_SEC)
        sigma_horizon = sigma_per_sec * math.sqrt(max(ttc, 0.0001))
        if sigma_horizon <= 0 or not math.isfinite(sigma_horizon):
            return self._skip_latarb('sigma_invalid')
        log_disp = math.log(price / open_price) if open_price > 0 else 0.0
        if not math.isfinite(log_disp):
            return self._skip_latarb('disp_invalid')
        if abs(log_disp) < 0.15 * sigma_horizon:
            return self._skip_latarb('disp_too_small')
        ito_drag = 0.5 * sigma_per_sec * sigma_per_sec * max(ttc, 0.0001)
        z = (log_disp - ito_drag) / sigma_horizon
        p_up = 0.5 * (1.0 + math.erf(z / math.sqrt(2.0)))
        model_prob = p_up if up else 1.0 - p_up
        model_prob = max(0.3, min(0.85, model_prob))
        if self.cfg.latency_arb_min_prob > 0.0 and model_prob < self.cfg.latency_arb_min_prob:
            return self._skip_latarb('prob_low')
        entry_vwap, _, entry_fillable = _entry_vwap_from_asks(book, self.cfg.min_order_size)
        if not entry_fillable or entry_vwap == float('inf') or entry_vwap <= 0 or (not math.isfinite(entry_vwap)):
            return self._skip_latarb('entry_unfillable')
        fee_rate = _market_fee_rate(mkt, self.cfg)
        fee_exp = _market_fee_exponent(mkt)
        taker_delay_buffer = 0.0  # N9 FIX: vestigial in live path too
        slippage = max(0.001, entry_vwap - ask)
        if fee_rate > 0:
            fee_per_share = _fee_per_share(fee_rate, entry_vwap, fee_exp)
        else:
            fee_per_share = self.cfg.taker_fee_bps * 0.0001 * entry_vwap
        edge = model_prob - ask - slippage - fee_per_share - taker_delay_buffer
        if edge < self.cfg.latency_arb_edge:
            return self._skip_latarb('edge_low')
        if book.top_depth_usdc < self.cfg.min_top_book_usdc:
            return self._skip_latarb('depth_low')
        if mkt.total_cost + self.cfg.min_order_size > self.cfg.max_position:
            return self._skip_latarb('position_cap', 'market total $%.2f + min $%.2f > max_position $%.2f', mkt.total_cost, self.cfg.min_order_size, self.cfg.max_position)
        strat = self.strategy
        if strat is not None:
            pending_total = sum(getattr(strat, '_pending_entry', {}).values())
            _net_cap, _gross_cap = strat.exposure_caps()
            if up:
                if strat._net_exposure + self.cfg.min_order_size + pending_total > _net_cap:
                    return self._skip_latarb('net_cap')
            elif strat._net_exposure - self.cfg.min_order_size - pending_total < -_net_cap:
                return self._skip_latarb('net_cap')
            if strat._gross_exposure + self.cfg.min_order_size + pending_total > _gross_cap:
                return self._skip_latarb('gross_cap')
            if strat._realized_loss.get(mkt.market_id, 0.0) <= -self.cfg.max_position:
                return self._skip_latarb('market_loss_cap')
            if not self.cfg.dry_run and self.cfg.min_order_size > strat.free_cash() + 1e-09:
                return self._skip_latarb('free_cash', 'min_order $%.2f > free cash $%.2f', self.cfg.min_order_size, strat.free_cash())
        if mkt.market_id in self._traded_entries:
            return self._skip_latarb('already_traded')
        if strat is not None and mkt.market_id in strat._traded:
            return self._skip_latarb('strategy_already_traded')
        if mkt.pos_yes.shares > 1e-06 or mkt.pos_no.shares > 1e-06:
            return self._skip_latarb('has_position')
        token = mkt.yes_token if up else mkt.no_token
        if self.polyfeed and time.monotonic() < self.polyfeed._last_large_trade_ts.get(token, 0.0) + self.cfg.whale_cooldown_s:
            return self._skip_latarb('whale_cooldown')
        if self.cfg.adverse_select_gate:
            adv = self.om.adverse_ewma('latarb')
            if adv is not None and adv > self.cfg.max_adverse_bps:
                self.log.info('SKIP LATARB %s: adverse EWMA %+.1fbps > cap %.1f â€” throttling FAK', coin, adv, self.cfg.max_adverse_bps)
                return self._skip_latarb('adverse_ewma')
            if adverse_gate(adv, book.mid, edge):
                self.log.info('SKIP LATARB %s: adverse EWMA eats edge %.3f', coin, edge)
                return self._skip_latarb('adverse_gate')
        tick = mkt.get_tick(token)
        dec, mt = mkt.tick_math(token)
        book = mkt.book_yes if up else mkt.book_no
        if book is None or book.is_crossed or book.is_stale(self.cfg.latarb_shadow_max_age_ms if self.cfg.latarb_shadow_max_age_ms > 0 else self.cfg.book_max_age_ms):
            return self._skip_latarb('recheck_stale')
        cur_ask = book.best_ask
        if cur_ask is None or cur_ask > ask + max(tick, 0.01):
            return self._skip_latarb('quote_moved', '%s %s ask moved %.3f -> %s', coin, mkt.market_id, ask, 'none' if cur_ask is None else f'{cur_ask:.3f}')
        # Size: min until live-proof GO; then depth-limited up to max_order_size.
        sz = self.cfg.min_order_size
        if self._live_proof_ok:
            target = self.cfg.max_order_size
            if strat is not None and not self.cfg.dry_run:
                target = min(target, max(0.0, strat.free_cash()))
            if _bankroll > 0:
                target = min(target, _bankroll * self.cfg.max_bankroll_fraction)
            target = max(self.cfg.min_order_size, target)
            lim, sized = _fak_limit_and_size(book, target, model_prob, fee_rate, taker_delay_buffer, self.cfg.latency_arb_edge, tick, dec, mt, self.cfg.min_order_size)
            if lim > 0 and sized >= self.cfg.min_order_size:
                sz = sized
                sweep = lim
            else:
                sweep = _fok_sweep_price(book, self.cfg.min_order_size, tick, dec, mt)
                sz = self.cfg.min_order_size
        else:
            lim, sized = _fak_limit_and_size(book, self.cfg.min_order_size, model_prob, fee_rate, taker_delay_buffer, self.cfg.latency_arb_edge, tick, dec, mt, self.cfg.min_order_size)
            if lim > 0 and sized >= self.cfg.min_order_size - 1e-09:
                sweep = lim
                sz = max(self.cfg.min_order_size, sized)
            else:
                sweep = _fok_sweep_price(book, self.cfg.min_order_size, tick, dec, mt)
                sz = self.cfg.min_order_size
        if sweep <= 0:
            return self._skip_latarb('sweep_unavailable')
        # P1: market-specific share minimum (V2 ConditionalToken size). If the
        # $ minimum is too small in shares, size up only when configured caps allow.
        mos = getattr(mkt, 'min_order_size', None)
        mos_val = float(mos) if mos is not None else 0.0
        if mos_val > 0.0:
            req_shares = sz / max(float(sweep), 0.001)
            if req_shares + 1e-12 < mos_val:
                needed_sz = math.ceil(mos_val * float(sweep) * 100.0) / 100.0
                needed_sz = max(self.cfg.min_order_size, needed_sz)
                if needed_sz > self.cfg.max_order_size + 1e-09:
                    return self._skip_latarb('mos_cap', 'market min shares %.4f need $%.2f at lim %.3f, max_order=$%.2f', mos_val, needed_sz, sweep, self.cfg.max_order_size)
                if mkt.total_cost + needed_sz > self.cfg.max_position + 1e-09:
                    return self._skip_latarb('position_cap', 'market total $%.2f + needed $%.2f > max_position $%.2f', mkt.total_cost, needed_sz, self.cfg.max_position)
                if strat is not None:
                    pending_total = sum(getattr(strat, '_pending_entry', {}).values())
                    _net_cap, _gross_cap = strat.exposure_caps()
                    if up:
                        if strat._net_exposure + needed_sz + pending_total > _net_cap + 1e-09:
                            return self._skip_latarb('net_cap', 'need $%.2f would exceed net cap $%.2f', needed_sz, _net_cap)
                    elif strat._net_exposure - needed_sz - pending_total < -_net_cap - 1e-09:
                        return self._skip_latarb('net_cap', 'need $%.2f would exceed short net cap $%.2f', needed_sz, _net_cap)
                    if strat._gross_exposure + needed_sz + pending_total > _gross_cap + 1e-09:
                        return self._skip_latarb('gross_cap', 'need $%.2f would exceed gross cap $%.2f', needed_sz, _gross_cap)
                    if not self.cfg.dry_run and needed_sz > strat.free_cash() + 1e-09:
                        return self._skip_latarb('free_cash', 'need $%.2f > free cash $%.2f', needed_sz, strat.free_cash())
                if _bankroll > 0 and needed_sz > _bankroll * self.cfg.max_bankroll_fraction + 1e-09:
                    return self._skip_latarb('bankroll_cap', 'need $%.2f > bankroll $%.2f * frac %.2f', needed_sz, _bankroll, self.cfg.max_bankroll_fraction)
                lim2, sized2 = _fak_limit_and_size(book, needed_sz, model_prob, fee_rate, taker_delay_buffer, self.cfg.latency_arb_edge, tick, dec, mt, needed_sz)
                if lim2 > 0 and sized2 >= needed_sz - 1e-09:
                    sweep = lim2
                    sz = sized2
                else:
                    sweep2 = _fok_sweep_price(book, needed_sz, tick, dec, mt)
                    if sweep2 <= 0:
                        return self._skip_latarb('mos_unfillable', 'market min shares %.4f need $%.2f but depth cannot fill', mos_val, needed_sz)
                    sweep = sweep2
                    sz = needed_sz
                req_shares = sz / max(float(sweep), 0.001)
                if req_shares + 1e-12 < mos_val:
                    return self._skip_latarb('mos_unfillable', 'market min shares %.4f still unmet: req %.4f at lim %.3f', mos_val, req_shares, sweep)
        entry_vwap2, _, fillable2 = _entry_vwap_from_asks(book, sz)
        if not fillable2 or entry_vwap2 == float('inf') or entry_vwap2 <= 0:
            return self._skip_latarb('entry_unfillable_final')
        if mkt.total_cost + sz > self.cfg.max_position + 1e-09:
            return self._skip_latarb('position_cap', 'market total $%.2f + size $%.2f > max_position $%.2f', mkt.total_cost, sz, self.cfg.max_position)
        if strat is not None:
            pending_total = sum(getattr(strat, '_pending_entry', {}).values())
            _net_cap, _gross_cap = strat.exposure_caps()
            if up:
                if strat._net_exposure + sz + pending_total > _net_cap + 1e-09:
                    return self._skip_latarb('net_cap', 'size $%.2f would exceed net cap $%.2f', sz, _net_cap)
            elif strat._net_exposure - sz - pending_total < -_net_cap - 1e-09:
                return self._skip_latarb('net_cap', 'size $%.2f would exceed short net cap $%.2f', sz, _net_cap)
            if strat._gross_exposure + sz + pending_total > _gross_cap + 1e-09:
                return self._skip_latarb('gross_cap', 'size $%.2f would exceed gross cap $%.2f', sz, _gross_cap)
            if not self.cfg.dry_run and sz > strat.free_cash() + 1e-09:
                return self._skip_latarb('free_cash', 'size $%.2f > free cash $%.2f', sz, strat.free_cash())
        fill_px = min(max(float(sweep), float(entry_vwap2)), 0.99)
        if fee_rate > 0:
            fee_fill = _fee_per_share(fee_rate, fill_px, fee_exp)
        else:
            fee_fill = self.cfg.taker_fee_bps * 0.0001 * fill_px
        edge_fill = model_prob - fill_px - fee_fill - taker_delay_buffer
        if edge_fill < self.cfg.latency_arb_edge:
            return self._skip_latarb('edge_fill_low')
        edge = edge_fill
        async with self._place_lock:
            if mkt.market_id in self._traded_entries or mkt.market_id in self._inflight:
                return self._skip_latarb('inflight_or_traded')
            if strat is not None and mkt.market_id in strat._traded:
                return self._skip_latarb('strategy_already_traded_lock')
            self._inflight.add(mkt.market_id)
            self._traded_entries.add(mkt.market_id)
            if strat is not None:
                strat._traded.add(mkt.market_id)
            if hasattr(mkt, 'latarb_hold_tokens'):
                mkt.latarb_hold_tokens.add(token)
            mkt.latarb_hold = True
            self.om.tag_entry_strategy(token, 'latarb')
            rkey = (mkt.market_id, token)
            if strat is not None:
                strat._pending_entry[rkey] = strat._pending_entry.get(rkey, 0.0) + sz
            self._cooldowns[mkt.market_id] = now + self.cfg.latency_arb_cooldown
        _log_key = mkt.market_id
        _prev_log = self._last_latarb_log.get(_log_key, 0.0)
        if time.monotonic() - _prev_log > 0.5:
            self._last_latarb_log[_log_key] = time.monotonic()
            self.log.info('LATARB %s %s | disp=%.4f | z=%.2f | ask=%.3f | lim=%.3f | sz=$%.2f | edge=%.3f | age=%.0fms | feeRate=%.4f', 'UP' if up else 'DN', coin, displacement, z, ask, sweep, sz, edge, book.age_ms, fee_rate)
        try:
            oid = await self.om.place(token, Side.BUY, sweep, sz, Strategy.TEMPORAL, otype='FAK', neg_risk=mkt.neg_risk, tick_size=tick, quote_ts=book.ts if book else None, max_quote_age_ms=self.cfg.latarb_shadow_max_age_ms if self.cfg.latarb_shadow_max_age_ms > 0.0 else None)
        except (Exception, asyncio.CancelledError):
            if strat is not None:
                strat._pending_entry[rkey] = max(0.0, strat._pending_entry.get(rkey, 0.0) - sz)
                if strat._pending_entry.get(rkey, 0.0) < 1e-09:
                    strat._pending_entry.pop(rkey, None)
                strat._traded.discard(mkt.market_id)
            self._traded_entries.discard(mkt.market_id)
            self._cooldowns.pop(mkt.market_id, None)
            self.om.clear_entry_strategy(token)
            if hasattr(mkt, 'latarb_hold_tokens'):
                mkt.latarb_hold_tokens.discard(token)
                if not mkt.latarb_hold_tokens:
                    mkt.latarb_hold = False
            else:
                mkt.latarb_hold = False
            raise
        finally:
            self._inflight.discard(mkt.market_id)
        # place() returns None on FAK zero-match; still re-check matched_size for partials.
        # P1: use actual tracked matched shares + avg fill only â€” never size/entry_vwap rewrite.
        matched_sz = 0.0
        actual_fill_px = 0.0
        if oid:
            tracked = self.om._orders.get(oid) if self.om is not None else None
            if tracked is not None:
                matched_sz = float(tracked.filled_size or 0.0)
                actual_fill_px = float(getattr(tracked, 'avg_fill_price', 0.0) or 0.0)
        filled = matched_sz > 1e-12
        req_shares = sz / max(float(sweep), 0.001)
        fill_frac = _latarb_fill_fraction(matched_sz, req_shares)
        self._record_fok_attempt(filled=filled, sweep=sweep, edge=edge, coin=coin, market_id=mkt.market_id, token=token, model_prob=model_prob, expected_vwap=float(entry_vwap2), matched_size=matched_sz, fill_fraction=fill_frac, actual_fill_px=actual_fill_px)
        if filled:
            mkt.latarb_hold = True
            if hasattr(mkt, 'latarb_hold_tokens'):
                mkt.latarb_hold_tokens.add(token)
            self.om.tag_entry_strategy(token, 'latarb')
        else:
            if strat is not None:
                strat._pending_entry[rkey] = max(0.0, strat._pending_entry.get(rkey, 0.0) - sz)
                if strat._pending_entry.get(rkey, 0.0) < 1e-09:
                    strat._pending_entry.pop(rkey, None)
                strat._traded.discard(mkt.market_id)
            self._traded_entries.discard(mkt.market_id)
            self.om.clear_entry_strategy(token)
            if hasattr(mkt, 'latarb_hold_tokens'):
                mkt.latarb_hold_tokens.discard(token)
                if not mkt.latarb_hold_tokens:
                    mkt.latarb_hold = False
            else:
                mkt.latarb_hold = False

    def _shadow_scan(self, coin: str, price: float, oracle_px: Optional[float]=None) -> None:
        try:
            markets = self.by_coin.get(coin, [])
            now = time.time()
            min_age = max(0.0, float(self.cfg.latarb_shadow_min_age_ms))
            throttle = self.cfg.latarb_shadow_throttle_ms / 1000.0
            for mkt in markets:
                if not mkt.end_time or not mkt.start_time or (not mkt.coin):
                    continue
                ttc = mkt.end_time - now
                # Evidence continues to expiry for close labeling; live entry remains >=30s in _eval_market.
                if ttc < 0 or ttc > mkt.tf_secs - 15:
                    continue
                by, bn = (mkt.book_yes, mkt.book_no)
                if not by or not bn:
                    continue
                if self.polyfeed is not None:
                    if not self.polyfeed.book_ready(mkt.yes_token) or not self.polyfeed.book_ready(mkt.no_token):
                        continue
                if by.is_crossed or bn.is_crossed:
                    continue
                open_price = self.tracker.get_price_at_or_before(coin, mkt.start_time, max_lag_s=10.0)
                if not open_price or open_price <= 0:
                    continue
                disp = (price - open_price) / open_price
                chosen_book = by if disp > 0 else bn
                if chosen_book.age_ms < min_age:
                    continue
                max_age = self.cfg.latarb_shadow_max_age_ms
                if max_age > 0.0 and chosen_book.age_ms > max_age:
                    continue
                if min(by.age_ms, bn.age_ms) > LATARB_DUAL_BOOK_STALE_MS:
                    continue
                near_close = ttc <= 5.0
                # After first candidate, only keep near-expiry rows for close labels.
                if mkt.market_id in self._shadow_candidate_logged and not near_close:
                    continue
                if not near_close and now - self._shadow_last.get(mkt.market_id, 0.0) < throttle:
                    continue
                self._shadow_last[mkt.market_id] = now
                self._shadow_log(now, mkt, coin, ttc, disp, price, open_price, by, bn, oracle_px=oracle_px)
        except Exception as e:
            self.log.warning('shadow scan error: %s', e)

    def _shadow_log(self, now, mkt, coin, ttc, disp, price, open_price, by, bn, oracle_px: Optional[float]=None) -> None:
        iso = datetime.fromtimestamp(now, tz=timezone.utc).isoformat(timespec='seconds').replace('+00:00', 'Z')
        up = disp > 0
        up_side = 'UP' if up else 'DN'
        chosen_book = by if up else bn
        chosen_token = mkt.yes_token if up else mkt.no_token
        ask = chosen_book.best_ask
        sigma_per_sec = max(self.tracker.volatility(coin), GBM_SIGMA_FLOOR_PER_SEC)
        ttc_eff = max(ttc, 0.0001)
        sigma_horizon = sigma_per_sec * math.sqrt(ttc_eff)
        log_disp = math.log(price / open_price) if open_price > 0 else 0.0
        ito_drag = 0.5 * sigma_per_sec * sigma_per_sec * ttc_eff
        z = (log_disp - ito_drag) / sigma_horizon if sigma_horizon > 0 and math.isfinite(log_disp) else 0.0
        p_up = 0.5 * (1.0 + math.erf(z / math.sqrt(2.0)))
        model_prob = p_up if up else 1.0 - p_up
        model_prob = max(0.3, min(0.85, model_prob))
        entry_vwap, _, entry_fillable = _entry_vwap_from_asks(chosen_book, self.cfg.min_order_size)
        sweep_price = 0.0
        slippage = 0.99
        fee_per_share = 0.0
        edge = -999.0
        oracle_price = float(oracle_px) if oracle_px is not None and oracle_px > 0 else None
        oracle_sign_ok: Optional[bool] = None
        if oracle_price is not None and open_price > 0:
            oracle_sign_ok = ((oracle_price - open_price) / open_price) * disp >= 0.0
        mos = getattr(mkt, 'min_order_size', None)
        mos_val = float(mos) if mos is not None else 0.0
        req_shares = 0.0
        fee_rate = _market_fee_rate(mkt, self.cfg)
        taker_delay_buffer = 0.0  # N9 FIX: vestigial (sigma~0.00025 â†’ buffer~0.0001 = 0.5% of edge threshold); removed to avoid false confidence
        if ask is not None and entry_fillable and (entry_vwap > 0) and math.isfinite(entry_vwap):
            slippage = max(0.001, entry_vwap - ask)
            fee_exp = _market_fee_exponent(mkt)
            if fee_rate > 0:
                fee_per_share = _fee_per_share(fee_rate, entry_vwap, fee_exp)
            else:
                fee_per_share = self.cfg.taker_fee_bps * 0.0001 * entry_vwap
            edge = model_prob - ask - slippage - fee_per_share - taker_delay_buffer
            tick = mkt.get_tick(chosen_token)
            dec, mt = mkt.tick_math(chosen_token)
            sweep_price = _fok_sweep_price(chosen_book, self.cfg.min_order_size, tick, dec, mt)
            # F2 parity: logged edge uses sweep fill when available (matches live gate).
            if sweep_price > 0:
                fill_px = float(sweep_price)  # N11/D6/N17 FIX: use sweep directly (actual FAK exec price); no vwap blend, no 0.99 cap
                if fee_rate > 0:
                    fee_per_share = _fee_per_share(fee_rate, fill_px, fee_exp)
                else:
                    fee_per_share = self.cfg.taker_fee_bps * 0.0001 * fill_px
                edge = model_prob - fill_px - fee_per_share - taker_delay_buffer
                slippage = max(0.001, fill_px - ask)
        if sweep_price > 0:
            req_shares = self.cfg.min_order_size / max(float(sweep_price), 0.001)
        max_order_shares = self.cfg.max_order_size / max(float(sweep_price), 0.001) if sweep_price > 0 else 0.0

        # Immutable first-signal candidate: match live LatArb gates (one per market).
        base_candidate = bool(
            ttc >= 30.0
            and entry_fillable
            and ask is not None and 0.0 < float(ask) <= 0.65
            and edge >= float(self.cfg.latency_arb_edge)
            and (self.cfg.latency_arb_min_prob <= 0.0 or model_prob >= float(self.cfg.latency_arb_min_prob))
            and chosen_book.top_depth_usdc >= float(self.cfg.min_top_book_usdc)
            and abs(log_disp) >= 0.15 * sigma_horizon
        )
        is_candidate = bool(
            base_candidate
            and oracle_sign_ok is not False
            and (mos_val <= 0.0 or max_order_shares + 1e-12 >= mos_val)
        )
        near_close = ttc <= 5.0
        if is_candidate:
            if mkt.market_id in self._shadow_candidate_logged and not near_close:
                return
            self._shadow_candidate_logged.add(mkt.market_id)
        elif not near_close and not base_candidate:
            # Drop non-signal mid-window spam; close rows still written for labels.
            return

        def f(x):
            return '' if x is None else f'{float(x):.6f}'
        strat = self.strategy
        net_exp = getattr(strat, '_net_exposure', None) if strat is not None else None
        gross_exp = getattr(strat, '_gross_exposure', None) if strat is not None else None
        row = ','.join([iso, f'{now:.3f}', str(mkt.market_id), coin, f'{ttc:.1f}', f'{disp:.6f}', up_side, f'{price:.4f}', f'{open_price:.4f}', f(by.best_bid), f(by.best_ask), f(bn.best_bid), f(bn.best_ask), f'{by.age_ms:.0f}', f'{bn.age_ms:.0f}', f'{sigma_per_sec:.10f}', f'{sigma_horizon:.10f}', f'{z:.6f}', f'{model_prob:.6f}', f'{entry_vwap:.6f}' if math.isfinite(entry_vwap) else '', f'{sweep_price:.6f}', f'{slippage:.6f}', f'{fee_per_share:.6f}', f'{edge:.6f}', f'{chosen_book.top_depth_usdc:.6f}', '1' if entry_fillable else '0', f(oracle_price), '' if oracle_sign_ok is None else ('1' if oracle_sign_ok else '0'), f(mos_val if mos_val > 0 else None), f(req_shares if req_shares > 0 else None), f(net_exp), f(gross_exp), f(mkt.total_cost)]) + '\n'
        try:
            self._shadow_pool.submit(self._write_shadow_row, row)
        except RuntimeError:
            pass

    def _write_shadow_row(self, line: str) -> None:
        try:
            f = self._shadow_fh
            if f is None:
                if self._shadow_init_done:
                    return
                self._shadow_init_done = True
                path = os.path.expanduser(self.cfg.latarb_shadow_path)
                header = 'ts_iso,ts_unix,market_id,coin,ttc,spot_disp,up_side,spot_price,open_price,yes_bid,yes_ask,no_bid,no_ask,yes_age_ms,no_age_ms,sigma_per_sec,sigma_horizon,z,model_prob,entry_vwap,sweep_price,slippage,fee_per_share,edge,top_depth_usdc,entry_fillable,oracle_price,oracle_sign_ok,mos,req_shares,net_exposure_usdc,gross_exposure_usdc,market_total_cost\n'
                need_header = not os.path.exists(path) or os.path.getsize(path) == 0
                os.makedirs(os.path.dirname(path) or '.', exist_ok=True)
                if os.path.exists(path) and os.path.getsize(path) > 0:
                    expected_cols = header.strip().count(',') + 1
                    corrupt_rows = False
                    with open(path, 'r', encoding='utf-8') as _rf:
                        existing_hdr = _rf.readline().strip()
                        if existing_hdr == header.strip():
                            for _ in range(200):
                                sample = _rf.readline()
                                if not sample:
                                    break
                                if sample.strip() and sample.rstrip('\n').count(',') + 1 != expected_cols:
                                    corrupt_rows = True
                                    break
                    if existing_hdr != header.strip() or corrupt_rows:
                        bak = '%s.bak.%d' % (path, int(time.time() * 1000))
                        os.replace(path, bak)
                        self.log.warning('LatArb shadow schema changed/corrupt; rotated stale log %s -> %s', path, bak)
                        need_header = True
                f = open(path, 'a', encoding='utf-8')
                self._shadow_fh = f
                if need_header:
                    f.write(header)
            f.write(line)
            self._shadow_writes += 1
            if self._shadow_writes % _CALIB_FLUSH_EVERY == 0:
                f.flush()
        except Exception as e:
            self.log.warning('shadow log write failed: %s', e)

    def close_shadow_log(self) -> None:
        pool = getattr(self, '_shadow_pool', None)
        if pool is not None:
            pool.shutdown(wait=True)
        fpool = getattr(self, '_fill_log_pool', None)
        if fpool is not None:
            try:
                fpool.shutdown(wait=True)
            except Exception:
                pass
        fh = self._shadow_fh
        if fh is not None and (not fh.closed):
            try:
                fh.flush()
                fh.close()
            except Exception as e:
                self.log.warning('shadow log close failed: %s', e)
        self._shadow_fh = None
        ls = self.fills_summary()
        if ls['attempts']:
            self.log.info('LatArb FOK session: attempts=%d fills=%d miss=%d rate=%.1f%% avg_edge=%.3f avg_slip=%.1fbps', ls['attempts'], ls['fills'], ls['misses'], 100.0 * ls['fill_rate'], ls['avg_edge'], ls['avg_slip_bps'])
_CTF_ADDRESS = '0x4D97Dcd97eC945f40cF65F87097ACe5EA0476045'
_CTF_COLLATERAL_ADAPTER = '0xAdA100Db00Ca00073811820692005400218FcE1f'
_NEG_RISK_COLLATERAL_ADAPTER = '0xadA2005600Dec949baf300f4C6120000bDB6eAab'
_PUSD_ADDRESS = '0xC011a7E12a19f7B1f670d46F03B03f3342E82DFB'
_HASH_ZERO = '0x' + '00' * 32
_ADAPTER_REDEEM_ABI = [
    {'inputs': [{'internalType': 'address', 'name': '', 'type': 'address'}, {'internalType': 'bytes32', 'name': '', 'type': 'bytes32'}, {'internalType': 'bytes32', 'name': '_conditionId', 'type': 'bytes32'}, {'internalType': 'uint256[]', 'name': '', 'type': 'uint256[]'}], 'name': 'redeemPositions', 'outputs': [], 'stateMutability': 'nonpayable', 'type': 'function'},
    {'anonymous': False, 'inputs': [{'indexed': True, 'internalType': 'address', 'name': 'initiator', 'type': 'address'}, {'indexed': True, 'internalType': 'bytes32', 'name': 'conditionId', 'type': 'bytes32'}, {'indexed': False, 'internalType': 'uint256[]', 'name': 'amounts', 'type': 'uint256[]'}, {'indexed': False, 'internalType': 'uint256', 'name': 'payout', 'type': 'uint256'}], 'name': 'PositionsRedeemed', 'type': 'event'},
]
_CTF_READ_ABI = [{'inputs': [{'internalType': 'bytes32', 'name': '', 'type': 'bytes32'}], 'name': 'payoutDenominator', 'outputs': [{'internalType': 'uint256', 'name': '', 'type': 'uint256'}], 'stateMutability': 'view', 'type': 'function'}, {'inputs': [{'internalType': 'bytes32', 'name': '', 'type': 'bytes32'}, {'internalType': 'uint256', 'name': '', 'type': 'uint256'}], 'name': 'payoutNumerators', 'outputs': [{'internalType': 'uint256', 'name': '', 'type': 'uint256'}], 'stateMutability': 'view', 'type': 'function'}, {'inputs': [{'internalType': 'address', 'name': 'account', 'type': 'address'}, {'internalType': 'address', 'name': 'operator', 'type': 'address'}], 'name': 'isApprovedForAll', 'outputs': [{'internalType': 'bool', 'name': '', 'type': 'bool'}], 'stateMutability': 'view', 'type': 'function'}]
_SAFE_EXEC_ABI = [{'inputs': [{'internalType': 'address', 'name': 'to', 'type': 'address'}, {'internalType': 'uint256', 'name': 'value', 'type': 'uint256'}, {'internalType': 'bytes', 'name': 'data', 'type': 'bytes'}, {'internalType': 'uint8', 'name': 'operation', 'type': 'uint8'}, {'internalType': 'uint256', 'name': 'safeTxGas', 'type': 'uint256'}, {'internalType': 'uint256', 'name': 'baseGas', 'type': 'uint256'}, {'internalType': 'uint256', 'name': 'gasPrice', 'type': 'uint256'}, {'internalType': 'address', 'name': 'gasToken', 'type': 'address'}, {'internalType': 'address', 'name': 'refundReceiver', 'type': 'address'}, {'internalType': 'bytes', 'name': 'signatures', 'type': 'bytes'}], 'name': 'execTransaction', 'outputs': [{'internalType': 'bool', 'name': 'success', 'type': 'bool'}], 'stateMutability': 'payable', 'type': 'function'}]
_REDEEM_POLL_S = 5.0
_REDEEM_REBROADCAST_S = 60.0
_REDEEM_STUCK_S = 1800.0

class RedemptionEngine:
    """Durable V2 redemption with signed intent persisted before broadcast."""

    _PERSIST_FIELDS = (
        'condition_id', 'neg_risk', 'shares_yes', 'shares_no', 'attempts',
        'callback_attempts', 'phase', 'tx_hash', 'raw_tx', 'nonce', 'target',
        'prepared_at', 'submitted_at', 'last_checked_at', 'confirmed_at',
        'receipt_block', 'receipt_payout', 'receipt_amounts', 'last_tx_hash',
        'last_error', 'terminal_error', 'fatal_notified',
    )

    def __init__(self, cfg: Config) -> None:
        self.cfg = cfg
        self.log = get_logger('Redeem', cfg.log_level)
        self._w3: Optional[Web3] = None
        self._acct = None
        self._done: Set[Tuple[str, str]] = set()
        self._queued: Set[Tuple[str, str]] = set()
        self._items: Dict[Tuple[str, str], dict] = {}
        self._resume_items: Dict[Tuple[str, str], dict] = {}
        self.on_state_change: Optional[Callable[[], None]] = None
        self.on_fatal: Optional[Callable[[str], None]] = None
        self._queue: 'asyncio.Queue[dict]' = asyncio.Queue()
        self._ready = False

    def _notify_state(self) -> None:
        if self.on_state_change is not None:
            self.on_state_change()

    def _is_safe(self) -> bool:
        return bool(self.cfg.use_proxy and self.cfg.signature_type == 2)

    def _holder(self) -> str:
        if self.cfg.signature_type == 1:
            raise RuntimeError('signature type 1 proxy redemption is unsupported (proxy-call ABI is not Safe execTransaction)')
        raw = self.cfg.proxy_address if self._is_safe() else self._acct.address
        return Web3.to_checksum_address(raw)

    def _init_web3(self) -> bool:
        if self._ready:
            return True
        if not self.cfg.redeem_enabled:
            return False
        if self.cfg.signature_type == 1:
            self.log.error('Redeem: refusing unsupported signature type 1 proxy routing')
            return False
        try:
            rpc = self.cfg.polygon_rpc_url
            self._w3 = Web3(Web3.HTTPProvider(rpc, request_kwargs={'timeout': 15}))
            if not self._w3.is_connected():
                self.log.error('Redeem: RPC %s not reachable', rpc)
                return False
            self._acct = Account.from_key(self.cfg.private_key)
            self._ready = True
            mode = 'Safe-proxy' if self._is_safe() else 'EOA'
            self.log.info('Redeem engine ready (mode=%s, signer=%s)', mode, self._acct.address)
            return True
        except Exception as e:
            self.log.error('Redeem init failed: %s', e)
            return False

    def preflight(self, require_standard: bool, require_neg_risk: bool) -> Tuple[bool, List[str]]:
        reasons: List[str] = []
        if not self.cfg.redeem_enabled:
            return (False, ['REDEEM_ENABLED=false'])
        if self.cfg.signature_type == 1:
            return (False, ['POLYMARKET_SIGNATURE_TYPE=1 redemption is unsupported; type-1 proxy calls do not use Safe execTransaction'])
        if not self._init_web3():
            return (False, [f'Polygon RPC unavailable: {self.cfg.polygon_rpc_url}'])
        w3 = self._w3
        try:
            if int(w3.eth.chain_id) != int(self.cfg.chain_id):
                reasons.append(f'RPC chain_id={w3.eth.chain_id}, expected {self.cfg.chain_id}')
            for label, address in (('CTF', _CTF_ADDRESS), ('pUSD', _PUSD_ADDRESS)):
                if not w3.eth.get_code(Web3.to_checksum_address(address)):
                    reasons.append(f'{label} has no bytecode at {address}')
            holder = self._holder()
            ctf = w3.eth.contract(address=Web3.to_checksum_address(_CTF_ADDRESS), abi=_CTF_READ_ABI)
            required = []
            if require_standard:
                required.append(('standard', _CTF_COLLATERAL_ADAPTER))
            if require_neg_risk:
                required.append(('neg-risk', _NEG_RISK_COLLATERAL_ADAPTER))
            for label, address in required:
                target = Web3.to_checksum_address(address)
                if not w3.eth.get_code(target):
                    reasons.append(f'{label} adapter has no bytecode at {address}')
                    continue
                if not bool(ctf.functions.isApprovedForAll(holder, target).call()):
                    reasons.append(f'holder {holder} has not approved {label} adapter {target} for CTF tokens')
        except Exception as e:
            reasons.append(f'redemption preflight RPC error: {e}')
        if not reasons:
            self.log.info('Redeem preflight passed (standard=%s neg_risk=%s)', require_standard, require_neg_risk)
        return (not reasons, reasons)

    def enqueue(self, condition_id: str, neg_risk: bool, shares_yes: float, shares_no: float, on_settled: Callable[[Optional[float], Optional[List[float]]], None]) -> bool:
        if not condition_id:
            self.log.warning('Redeem: missing condition_id â€” cannot enqueue; settlement metadata retained')
            return False
        key = (condition_id, 'neg' if neg_risk else 'ctf')
        if key in self._done or key in self._queued:
            return False
        self._queued.add(key)
        item = {'condition_id': condition_id, 'neg_risk': bool(neg_risk), 'shares_yes': max(0.0, float(shares_yes)), 'shares_no': max(0.0, float(shares_no)), 'on_settled': on_settled, 'attempts': 0, 'callback_attempts': 0, 'phase': 'queued'}
        resume = self._resume_items.pop(key, None) or {}
        for field in self._PERSIST_FIELDS:
            if field in resume:
                item[field] = resume[field]
        self._items[key] = item
        self._queue.put_nowait(item)
        self._notify_state()
        return True

    @staticmethod
    def _is_terminal_phase(phase: str) -> bool:
        return phase in ('nonce_conflict', 'receipt_error', 'stuck')

    async def run(self) -> None:
        if not self.cfg.redeem_enabled:
            self.log.info('Redeem engine disabled (REDEEM_ENABLED=false) â€” winning legs settle as soft estimates only')
            return
        loop = asyncio.get_running_loop()
        while True:
            item = await self._queue.get()
            key = (item['condition_id'], 'neg' if item.get('neg_risk') else 'ctf')
            delay = 0.0
            try:
                updates = await loop.run_in_executor(None, self._advance_redeem, dict(item))
                next_delay = float(updates.pop('_next_delay', 0.0) or 0.0)
                for k, v in updates.items():
                    if v is None:
                        item.pop(k, None)
                    else:
                        item[k] = v
                self._notify_state()
                phase = str(item.get('phase') or 'queued')
                if phase == 'confirmed':
                    try:
                        item['on_settled'](float(item['receipt_payout']), list(item.get('receipt_amounts') or []))
                    except Exception as e:
                        item['callback_attempts'] = int(item.get('callback_attempts', 0)) + 1
                        item['last_error'] = f'settlement callback: {e}'
                        self.log.error('Redeem settlement callback failed for %s: %s', item.get('condition_id', '?')[:18], e)
                        self._notify_state()
                        delay = min(300.0, float(2 ** min(item['callback_attempts'], 8)))
                    else:
                        self._done.add(key)
                        self._queued.discard(key)
                        self._items.pop(key, None)
                        self._notify_state()
                        self.log.info('REDEEM APPLIED %s | payout=$%.6f tx=%s', item['condition_id'][:18], float(item['receipt_payout']), str(item.get('tx_hash') or '?')[:18])
                        continue
                elif self._is_terminal_phase(phase):
                    reason = str(item.get('terminal_error') or phase)
                    if not item.get('fatal_notified'):
                        item['fatal_notified'] = True
                        if self.on_fatal is not None:
                            self.on_fatal(reason)
                        self._notify_state()
                    delay = 60.0
                elif phase == 'prepared':
                    delay = 0.0
                else:
                    delay = next_delay or _REDEEM_POLL_S
            except asyncio.CancelledError:
                raise
            except Exception as e:
                item['attempts'] = int(item.get('attempts', 0)) + 1
                item['last_error'] = str(e)
                delay = min(300.0, float(2 ** min(item['attempts'], 8)))
                self.log.warning('Redeem retry %d for %s in %.0fs: %s', item['attempts'], item.get('condition_id', '?')[:18], delay, e)
                self._notify_state()
            finally:
                self._queue.task_done()
            if key in self._items:
                if delay > 0:
                    await asyncio.sleep(delay)
                self._queue.put_nowait(item)

    def _condition_bytes(self, cid: str) -> bytes:
        try:
            cond = Web3.to_bytes(hexstr=cid)
        except Exception as e:
            raise RuntimeError(f'malformed condition_id {cid!r}') from e
        if len(cond) != 32:
            raise RuntimeError(f'condition_id {cid!r} is not 32 bytes')
        return cond

    def _receipt_or_none(self, tx_hash: str) -> Optional[dict]:
        try:
            return self._w3.eth.get_transaction_receipt(tx_hash)
        except TransactionNotFound:
            return None

    def _decode_redemption_receipt(self, receipt: dict, target: str, cond: bytes, holder: str) -> Tuple[float, List[float]]:
        adapter = self._w3.eth.contract(address=Web3.to_checksum_address(target), abi=_ADAPTER_REDEEM_ABI)
        decoded = adapter.events.PositionsRedeemed().process_receipt(receipt)
        matches = []
        for event in decoded:
            args = event.get('args') or {}
            try:
                initiator = Web3.to_checksum_address(args.get('initiator'))
                event_cond = bytes(args.get('conditionId'))
            except Exception:
                continue
            if initiator.lower() == holder.lower() and event_cond == bytes(cond):
                matches.append(args)
        if len(matches) != 1:
            raise RuntimeError(f'expected exactly one matching PositionsRedeemed event, got {len(matches)}')
        args = matches[0]
        raw_amounts = list(args.get('amounts') or [])
        if len(raw_amounts) != 2 or any(int(v) < 0 for v in raw_amounts):
            raise RuntimeError(f'invalid PositionsRedeemed amounts: {raw_amounts!r}')
        payout_raw = int(args.get('payout'))
        if payout_raw < 0:
            raise RuntimeError(f'invalid PositionsRedeemed payout: {payout_raw}')
        return (payout_raw / _USDC_SCALE, [int(v) / _USDC_SCALE for v in raw_amounts])

    def _finalize_receipt(self, item: dict, receipt: dict, cond: bytes, target: str, holder: str) -> dict:
        tx_hash = str(item.get('tx_hash') or '')
        status = int(receipt.get('status') or 0)
        if status != 1:
            self.log.error('Redeem tx %s reverted on-chain (status=%s)', tx_hash[:18], status)
            return {'phase': 'queued', 'last_tx_hash': tx_hash, 'tx_hash': None, 'raw_tx': None, 'nonce': None, 'prepared_at': None, 'submitted_at': None, 'last_error': f'transaction reverted status={status}'}
        try:
            payout, amounts = self._decode_redemption_receipt(receipt, target, cond, holder)
        except Exception as e:
            return {'phase': 'receipt_error', 'terminal_error': f'confirmed redemption receipt cannot be accounted: {e}', 'receipt_block': int(receipt.get('blockNumber') or 0), '_next_delay': 60.0}
        self.log.info('REDEEM CONFIRMED %s via %s | payout=$%.6f amounts=%s tx=%s', item['condition_id'][:18], 'neg-v2' if item.get('neg_risk') else 'ctf-v2', payout, amounts, tx_hash[:18])
        return {'phase': 'confirmed', 'confirmed_at': time.time(), 'receipt_block': int(receipt.get('blockNumber') or 0), 'receipt_payout': float(payout), 'receipt_amounts': amounts, 'last_error': None, 'terminal_error': None}

    def _advance_redeem(self, item: dict) -> dict:
        if not self._init_web3():
            raise RuntimeError('redemption Web3 initialization failed')
        cid = str(item['condition_id'])
        cond = self._condition_bytes(cid)
        neg_risk = bool(item.get('neg_risk'))
        target = _NEG_RISK_COLLATERAL_ADAPTER if neg_risk else _CTF_COLLATERAL_ADAPTER
        holder = self._holder()
        tx_hash = str(item.get('tx_hash') or '')
        phase = str(item.get('phase') or 'queued')
        if tx_hash:
            receipt = self._receipt_or_none(tx_hash)
            if receipt is not None:
                return self._finalize_receipt(item, receipt, cond, target, holder)
            if self._is_terminal_phase(phase):
                return {'last_checked_at': time.time(), '_next_delay': 60.0}
            raw_hex = str(item.get('raw_tx') or '')
            if not raw_hex:
                return {'phase': 'nonce_conflict', 'terminal_error': 'persisted redemption hash has no signed raw transaction; safe rebroadcast is impossible', 'last_checked_at': time.time(), '_next_delay': 60.0}
            known = False
            try:
                self._w3.eth.get_transaction(tx_hash)
                known = True
            except TransactionNotFound:
                known = False
            age = max(0.0, time.time() - float(item.get('submitted_at') or item.get('prepared_at') or time.time()))
            if known:
                if age >= _REDEEM_STUCK_S:
                    return {'phase': 'stuck', 'terminal_error': f'redemption transaction pending for {age:.0f}s; operator reconciliation required', 'last_checked_at': time.time(), '_next_delay': 60.0}
                return {'phase': 'submitted', 'last_checked_at': time.time(), '_next_delay': _REDEEM_POLL_S}
            if phase == 'submitted' and age < _REDEEM_REBROADCAST_S:
                return {'last_checked_at': time.time(), '_next_delay': min(_REDEEM_POLL_S, _REDEEM_REBROADCAST_S - age)}
            raw = Web3.to_bytes(hexstr=raw_hex)
            expected_hash = Web3.to_hex(Web3.keccak(raw)).lower()
            if expected_hash != tx_hash.lower():
                return {'phase': 'nonce_conflict', 'terminal_error': 'persisted raw transaction hash does not match tx_hash', 'last_checked_at': time.time(), '_next_delay': 60.0}
            try:
                sent = self._w3.eth.send_raw_transaction(raw)
                sent_hex = Web3.to_hex(sent)
                if sent_hex.lower() != tx_hash.lower():
                    raise RuntimeError(f'RPC returned unexpected transaction hash {sent_hex}')
            except Exception as e:
                msg = str(e).lower()
                if 'already known' not in msg and 'known transaction' not in msg and 'replacement transaction underpriced' not in msg:
                    if 'nonce too low' in msg:
                        latest_nonce = int(self._w3.eth.get_transaction_count(self._acct.address, 'latest'))
                        saved_nonce = int(item.get('nonce', -1))
                        if saved_nonce >= 0 and latest_nonce > saved_nonce:
                            return {'phase': 'nonce_conflict', 'terminal_error': f'redemption nonce {saved_nonce} was consumed but persisted hash has no receipt', 'last_checked_at': time.time(), '_next_delay': 60.0}
                    raise
            return {'phase': 'submitted', 'submitted_at': time.time(), 'last_checked_at': time.time(), 'last_error': None, '_next_delay': _REDEEM_POLL_S}
        ctf = self._w3.eth.contract(address=Web3.to_checksum_address(_CTF_ADDRESS), abi=_CTF_READ_ABI)
        denominator = int(ctf.functions.payoutDenominator(cond).call() or 0)
        if denominator <= 0:
            raise RuntimeError('condition is not resolved on-chain yet')
        target_cs = Web3.to_checksum_address(target)
        if not bool(ctf.functions.isApprovedForAll(holder, target_cs).call()):
            raise RuntimeError(f'holder {holder} has not approved V2 adapter {target_cs} for CTF tokens')
        adapter = self._w3.eth.contract(address=target_cs, abi=_ADAPTER_REDEEM_ABI)
        inner = adapter.encode_abi('redeemPositions', args=[Web3.to_checksum_address(_PUSD_ADDRESS), _HASH_ZERO, cond, [1, 2]])
        prepared = self._prepare_safe(target, inner) if self._is_safe() else self._prepare_direct(target, inner)
        return {'phase': 'prepared', 'target': target, 'tx_hash': prepared['tx_hash'], 'raw_tx': prepared['raw_tx'], 'nonce': prepared['nonce'], 'prepared_at': time.time(), 'submitted_at': None, 'last_checked_at': None, 'last_error': None, 'terminal_error': None, '_next_delay': 0.0}

    def reconcile_saved_receipts(self, state: dict) -> bool:
        """Read-only receipt reconciliation used before the live position barrier."""
        rows = state.get('redemptions', []) if isinstance(state, dict) else []
        if not rows:
            return False
        if not self._init_web3():
            raise RuntimeError('cannot reconcile persisted redemption receipts: Web3 initialization failed')
        changed = False
        for row in rows:
            if not isinstance(row, dict) or not row.get('tx_hash') or row.get('phase') == 'confirmed':
                continue
            receipt = self._receipt_or_none(str(row['tx_hash']))
            if receipt is None:
                continue
            cond = self._condition_bytes(str(row.get('condition_id') or ''))
            target = _NEG_RISK_COLLATERAL_ADAPTER if bool(row.get('neg_risk')) else _CTF_COLLATERAL_ADAPTER
            updates = self._finalize_receipt(row, receipt, cond, target, self._holder())
            for k, v in updates.items():
                if k.startswith('_'):
                    continue
                if v is None:
                    row.pop(k, None)
                else:
                    row[k] = v
            changed = True
        return changed

    def _gas_kwargs(self) -> dict:
        base = int(self._w3.eth.gas_price)
        cap = int(float(self.cfg.redeem_max_gas_gwei) * 1_000_000_000.0)
        if cap > 0 and base > cap:
            raise RuntimeError(f'current gas price {base / 1e9:.3f} gwei exceeds redemption cap {cap / 1e9:.3f} gwei')
        max_fee = min(base * 2, cap) if cap > 0 else base * 2
        priority = min(2_000_000_000, max(0, max_fee - base))
        return {'maxFeePerGas': int(max_fee), 'maxPriorityFeePerGas': int(priority)}

    def _signed_payload(self, tx: dict) -> dict:
        signed = self._acct.sign_transaction(tx)
        raw = bytes(signed.raw_transaction)
        return {'raw_tx': Web3.to_hex(raw), 'tx_hash': Web3.to_hex(Web3.keccak(raw)), 'nonce': int(tx['nonce'])}

    def _prepare_direct(self, target: str, data: str) -> dict:
        w3 = self._w3
        eoa = self._acct.address
        tx = {'to': Web3.to_checksum_address(target), 'from': eoa, 'data': data, 'nonce': w3.eth.get_transaction_count(eoa, 'pending'), 'chainId': self.cfg.chain_id, **self._gas_kwargs()}
        tx['gas'] = int(w3.eth.estimate_gas(tx) * 1.3)
        return self._signed_payload(tx)

    def _prepare_safe(self, target: str, inner_data: str) -> dict:
        if not self._is_safe():
            raise RuntimeError('Safe redemption requested for a non-type-2 account')
        w3 = self._w3
        eoa = self._acct.address
        safe_addr = Web3.to_checksum_address(self.cfg.proxy_address)
        safe = w3.eth.contract(address=safe_addr, abi=_SAFE_EXEC_ABI)
        owner_padded = bytes(12) + Web3.to_bytes(hexstr=eoa)
        sig = owner_padded + bytes(32) + bytes([1])
        fn = safe.functions.execTransaction(Web3.to_checksum_address(target), 0, Web3.to_bytes(hexstr=inner_data), 0, 0, 0, 0, '0x0000000000000000000000000000000000000000', '0x0000000000000000000000000000000000000000', sig)
        tx = fn.build_transaction({'from': eoa, 'nonce': w3.eth.get_transaction_count(eoa, 'pending'), 'chainId': self.cfg.chain_id, **self._gas_kwargs()})
        tx['gas'] = int(w3.eth.estimate_gas(tx) * 1.3)
        return self._signed_payload(tx)

class Risk:

    def __init__(self, cfg: Config, om: OrderManager) -> None:
        self.cfg = cfg
        self.om = om
        self.log = get_logger('Risk', cfg.log_level)
        self._halted = False
        self._reason = ''
        self._halt_type = ''
        self._pnl = 0.0
        self._pnl_peak = 0.0
        self._day_start = 0.0
        self._day_reset = time.monotonic()
        self._consecutive_losses = 0
        self._month_start = 0.0
        self._month_reset = time.monotonic()
        self._bankroll_ref: Optional[Callable[[], float]] = None
        self.on_state_change: Optional[Callable[[], None]] = None

    @property
    def halted(self) -> bool:
        return self._halted

    def record_pnl(self, delta: float) -> None:
        self._pnl += delta

    def record_trade_closed(self, net_pnl: float) -> None:
        if net_pnl < 0:
            self._consecutive_losses += 1
        elif net_pnl > 0:
            self._consecutive_losses = 0

    def ok(self) -> bool:
        if self.om.fill_apply_error:
            if not self._halted or self._halt_type != 'fill_durability':
                self._halt(f'fill durability failure: {self.om.fill_apply_error}', halt_type='fill_durability')
            return False
        if time.monotonic() - self._day_reset > 86400:
            self._day_start = self._pnl
            self._day_reset = time.monotonic()
            if self._halted:
                if self._halt_type in ('daily_loss', 'consec_losses'):
                    _cleared_type = self._halt_type
                    self._halted = False
                    self._reason = ''
                    self._halt_type = ''
                    self._consecutive_losses = 0
                    self.log.info('Daily reset â€” halt cleared (type was %s)', _cleared_type)
                else:
                    self.log.warning('Daily reset â€” halt NOT cleared (type=%s requires operator)', self._halt_type)
        if self._halted and self._halt_type == 'rejects' and (self.om.rejects < 5):
            self.log.info('Reject-halt auto-cleared â€” venue recovered (reject count back to %d)', self.om.rejects)
            self._halted = False
            self._reason = ''
            self._halt_type = ''
        if self._halted:
            return False
        dp = self._pnl - self._day_start
        bankroll = 0.0
        if self._bankroll_ref is not None:
            try:
                bankroll = max(0.0, float(self._bankroll_ref() or 0.0))
            except Exception:
                bankroll = 0.0
        # Pct-of-bankroll is primary when known; hard-dollar is fallback when bankroll unknown.
        if bankroll > 0.0 and self.cfg.max_daily_loss_pct > 0.0:
            daily_cap = bankroll * self.cfg.max_daily_loss_pct
        else:
            daily_cap = self.cfg.max_daily_loss
        if dp < -daily_cap:
            self._halt(f'Daily loss ${-dp:.2f} (cap ${daily_cap:.2f})', halt_type='daily_loss')
            return False
        if self._pnl > self._pnl_peak:
            self._pnl_peak = self._pnl
        if bankroll > 0.0 and self.cfg.max_daily_loss_pct > 0.0:
            dd_cap = bankroll * self.cfg.max_daily_loss_pct
        else:
            dd_cap = self.cfg.max_drawdown_from_peak
        if dd_cap > 0.0:
            dd = self._pnl_peak - self._pnl
            if dd > dd_cap:
                self._halt(f'Drawdown ${dd:.2f} from peak ${self._pnl_peak:.2f} (cap ${dd_cap:.2f})', halt_type='drawdown')
                return False
        if time.monotonic() - self._month_reset > 30 * 86400:
            self._month_start = self._pnl
            self._month_reset = time.monotonic()
        mp = self._pnl - self._month_start
        if mp < -self.cfg.max_monthly_loss:
            self._halt(f'Monthly loss ${-mp:.2f}', halt_type='monthly_loss')
            return False
        if self.om.rejects >= 5:
            self._halt(f'{self.om.rejects} consecutive order rejects', halt_type='rejects')
            return False
        if self._consecutive_losses >= self.cfg.max_consecutive_losses:
            self._halt(f'{self._consecutive_losses} consecutive losses', halt_type='consec_losses')
            return False
        if self.om.count >= self.cfg.max_open_orders:
            return False
        return True

    def _halt(self, reason: str, halt_type: str='unknown') -> None:
        self._halted = True
        self._reason = reason
        self._halt_type = halt_type
        self.log.critical('HALT [%s]: %s', halt_type, reason)
        if self.on_state_change is not None:
            self.on_state_change()

    def status(self) -> dict:
        dp = self._pnl - self._day_start
        return {'pnl': round(self._pnl, 4), 'daily': round(dp, 4), 'orders': self.om.count, 'halted': self._halted, 'halt_type': self._halt_type, 'reason': self._reason, 'consec_losses': self._consecutive_losses}

class Bot:

    def __init__(self, cfg: Config) -> None:
        self.cfg = cfg
        self.log = get_logger('Bot', cfg.log_level)
        self.metrics = Metrics() if cfg.metrics_enabled else None
        self.client = PolyClient(cfg)
        self.om = OrderManager(cfg, self.client, self.metrics)
        self.risk = Risk(cfg, self.om)
        self.om.on_fill_failure = lambda reason: self.risk._halt(f'fill durability failure: {reason}', halt_type='fill_durability')
        self.redeemer = RedemptionEngine(cfg)
        self._state_identity: Optional[dict] = None
        self._state_path: str = ''
        self._loaded_state: dict = {}
        self.binance = BinanceFeed(cfg.coins)
        self.chainlink = ChainlinkFeed(cfg.coins)
        self.polyfeed = HyperPolyFeed(shard_count=cfg.ws_shard_count)
        self.polyfeed._whale_threshold_usdc = cfg.whale_trade_usdc
        self.userfeed: Optional[UserFeed] = None
        self.tracker: Optional[PriceTracker] = None
        self.fivemin: Optional[FiveMinStrategy] = None
        self.latency_arb: Optional[LatencyArb] = None
        self.fivemin_markets: List[Market] = []
        self._5m_ids: Set[str] = set()
        self.markets: List[Market] = []
        self.t2m: Dict[str, Market] = {}
        self.by_coin: Dict[str, List[Market]] = {}
        self.tasks: List[asyncio.Task] = []
        self._eval_tasks: Set[asyncio.Task] = set()
        self._bg_tasks: Set[asyncio.Task] = set()
        self.running = False
        self.shutdown_ev = asyncio.Event()
        self.session: Optional[aiohttp.ClientSession] = None
        self._pos_lock = asyncio.Lock()
        self._trade_pnl_in_flight: Dict[Tuple[str, str], float] = {}
        self._applied_trade_order: Deque[str] = deque(maxlen=10000)
        self._applied_trade_ids: Set[str] = set()
        self._applied_ioc_order: Deque[str] = deque(maxlen=10000)
        self._applied_ioc_order_ids: Set[str] = set()
        self._drift_io_pool = concurrent.futures.ThreadPoolExecutor(max_workers=max(1, int(self.cfg.drift_check_concurrency)), thread_name_prefix='drift-io')

    async def run(self) -> None:
        self.session = aiohttp.ClientSession(connector=aiohttp.TCPConnector(limit=60), timeout=aiohttp.ClientTimeout(total=10), headers={'Accept': 'application/json'})
        try:
            await self._boot()
        except FatalBotError:
            raise
        except (KeyboardInterrupt, asyncio.CancelledError):
            self.log.warning('Interrupt received â€” running graceful shutdown')
            try:
                await self._shutdown()
            except Exception as se:
                self.log.error('Graceful shutdown error: %s', se)
        except Exception as e:
            self.log.critical('Boot failed: %s', e, exc_info=True)
            raise
        finally:
            if self.session and (not self.session.closed):
                await self.session.close()
            self.client.close()

    @staticmethod
    def _remember_bounded(value: str, order: Deque[str], values: Set[str]) -> None:
        if not value or value in values:
            return
        if order.maxlen is not None and len(order) == order.maxlen:
            values.discard(order[0])
        order.append(value)
        values.add(value)

    def _remember_applied_fill(self, trade_id: str, ioc_order_ids: Optional[Set[str]]=None) -> None:
        self._remember_bounded(str(trade_id or ''), self._applied_trade_order, self._applied_trade_ids)
        for order_id in ioc_order_ids or set():
            self._remember_bounded(str(order_id or ''), self._applied_ioc_order, self._applied_ioc_order_ids)

    def _configure_runtime_state(self) -> None:
        holder = str(self.client.trading_address or self.cfg.proxy_address or self.client.signer_address or '')
        if self.cfg.dry_run and not holder:
            holder = 'paper'
        try:
            self._state_identity = _runtime_state_identity(holder, self.cfg.chain_id, self.cfg.dry_run)
            self._state_path = _latarb_state_path(self._state_identity)
            self._loaded_state = _load_latarb_state(self._state_path, self._state_identity, strict=not self.cfg.dry_run)
        except RuntimeStateError as e:
            raise FatalBotError(f'Runtime-state safety check failed: {e}') from e
        self.log.info('Runtime state: %s (%s)', self._state_path, 'restored' if self._loaded_state else 'new')

    def _save_runtime_state(self) -> None:
        if self._state_identity is None or not self._state_path:
            return
        self._loaded_state = _snapshot_runtime_state(self.markets, self.fivemin, self.risk, self.redeemer, self.cfg.dry_run, self._state_identity, self._state_path, self._trade_pnl_in_flight, self.om, self._applied_trade_order, self._applied_ioc_order)

    async def _reconcile_saved_redemptions_before_position_barrier(self) -> None:
        if self.cfg.dry_run or not self._loaded_state or not self._loaded_state.get('redemptions'):
            return
        try:
            changed = await asyncio.get_running_loop().run_in_executor(None, self.redeemer.reconcile_saved_receipts, self._loaded_state)
            if changed:
                _save_latarb_state(self._loaded_state, self._state_path, self._state_identity)
                self.log.warning('Recovered confirmed redemption receipt(s) before live position reconciliation')
        except Exception as e:
            raise FatalBotError(f'Persisted redemption receipt reconciliation failed: {e}') from e

    async def _verify_live_position_state(self) -> None:
        if self.cfg.dry_run:
            return
        holder = self.client.trading_address
        if not holder:
            raise FatalBotError('Live position recovery: trading address is unavailable')
        state = self._loaded_state
        expected: Dict[str, float] = {}
        expected_cond: Dict[str, str] = {}
        if state:
            for row in state.get('markets', {}).values():
                if not isinstance(row, dict):
                    continue
                cond = str(row.get('condition_id') or '')
                for token_key, pos_key in (('yes_token', 'pos_yes'), ('no_token', 'pos_no')):
                    token = str(row.get(token_key) or '')
                    shares = max(0.0, float((row.get(pos_key) or {}).get('shares', 0.0) or 0.0))
                    if token and shares > 1e-09:
                        expected[token] = max(expected.get(token, 0.0), shares)
                        expected_cond[token] = cond
            for entry in state.get('redeem_meta', []):
                if not isinstance(entry, dict) or not isinstance(entry.get('meta'), dict):
                    continue
                meta = entry['meta']
                token = str(entry.get('token_id') or meta.get('token_id') or '')
                shares = max(0.0, float(meta.get('shares', 0.0) or 0.0))
                if token and shares > 1e-09:
                    expected[token] = max(expected.get(token, 0.0), shares)
                    expected_cond[token] = str(meta.get('condition_id') or '')
        # A receipt-confirmed adapter redemption burns the event's exact amounts.
        # Reconcile those before comparing against the Data API, then let the
        # idempotent settlement callback retire local inventory after restore.
        rows_by_condition = {str(row.get('condition_id') or '').lower(): row for row in state.get('markets', {}).values() if isinstance(row, dict)}
        for item in state.get('redemptions', []):
            if not isinstance(item, dict) or item.get('phase') != 'confirmed':
                continue
            kind = 'neg' if bool(item.get('neg_risk')) else 'ctf'
            ledger_id = f'{str(item.get("condition_id") or "").lower()}:{kind}'
            if (state.get('settlement_ledger', {}).get(ledger_id) or {}).get('phase') == 'booked':
                continue
            amounts = item.get('receipt_amounts') or []
            row = rows_by_condition.get(str(item.get('condition_id') or '').lower())
            if row is None or len(amounts) != 2:
                raise FatalBotError('Confirmed redemption state lacks a matching market row or authoritative two-leg amounts')
            for token_key, amount in (('yes_token', amounts[0]), ('no_token', amounts[1])):
                token = str(row.get(token_key) or '')
                if token:
                    expected[token] = max(0.0, expected.get(token, 0.0) - float(amount))
        expected = {token: shares for token, shares in expected.items() if shares >= max(1e-06, self.cfg.drift_halt_threshold_shares)}
        remote: Dict[str, Tuple[float, str]] = {}
        offset = 0
        while offset < 5000:
            try:
                async with self.session.get('https://data-api.polymarket.com/positions', params={'user': holder, 'sizeThreshold': '0', 'limit': '500', 'offset': str(offset)}, timeout=aiohttp.ClientTimeout(total=15)) as r:
                    if not r.ok:
                        raise FatalBotError(f'Live position recovery: Data API HTTP {r.status}')
                    payload = await r.json(content_type=None)
            except FatalBotError:
                raise
            except Exception as e:
                raise FatalBotError(f'Live position recovery: Data API unavailable: {e}') from e
            if not isinstance(payload, list):
                raise FatalBotError(f'Live position recovery: malformed Data API payload ({type(payload).__name__})')
            for row in payload:
                if not isinstance(row, dict):
                    continue
                token = str(row.get('asset') or '')
                try:
                    shares = max(0.0, float(row.get('size') or 0.0))
                except (TypeError, ValueError):
                    raise FatalBotError(f'Live position recovery: malformed size for token {token[:16]}')
                if token and shares >= self.cfg.drift_halt_threshold_shares:
                    remote[token] = (shares, str(row.get('conditionId') or row.get('condition_id') or ''))
            if len(payload) < 500:
                break
            offset += 500
        else:
            raise FatalBotError('Live position recovery: more than 5000 positions; pagination bound exceeded')
        mismatches: List[str] = []
        tolerance = max(1e-06, self.cfg.drift_halt_threshold_shares)
        for token, (shares, cond) in remote.items():
            local = expected.get(token)
            if local is None:
                mismatches.append(f'unowned remote token {token[:16]} shares={shares:.6f} condition={cond[:18]}')
            elif abs(local - shares) >= tolerance:
                mismatches.append(f'token {token[:16]} state={local:.6f} remote={shares:.6f}')
            elif expected_cond.get(token) and cond and expected_cond[token].lower() != cond.lower():
                mismatches.append(f'token {token[:16]} condition mismatch state={expected_cond[token][:18]} remote={cond[:18]}')
        for token, shares in expected.items():
            if shares >= tolerance and token not in remote:
                mismatches.append(f'persisted token {token[:16]} shares={shares:.6f} absent remotely')
        if mismatches:
            for mismatch in mismatches[:20]:
                self.log.critical('POSITION RECOVERY MISMATCH: %s', mismatch)
            raise FatalBotError(f'Live position recovery failed with {len(mismatches)} mismatch(es); refusing any order')
        self.log.info('Live position recovery barrier OK: %d remote position(s), %d persisted position(s)', len(remote), len(expected))

    async def _boot(self) -> None:
        self._banner()
        try:
            async with self.session.get(f'{self.cfg.clob_url}/') as r:
                if r.status not in (200, 404):
                    raise ConnectionError(f'CLOB returned HTTP {r.status}')
            self.log.info('CLOB reachable')
        except Exception as e:
            self.log.critical('CLOB unreachable: %s', e)
            raise FatalBotError(f'CLOB unreachable: {e}')
        self.log.info('Polymarket SDK: %s', 'py-clob-client-v2 (CLOB V2)' if _SDK_IS_V2 else 'py-clob-client V1 â€” DEAD, orders WILL be rejected' if _HAS_SDK else 'NOT INSTALLED')
        ok = await self.client.initialize(self.session)
        if not ok:
            self.log.critical('Authentication failed.\n  Check: POLYMARKET_PRIVATE_KEY, POLYMARKET_PROXY_ADDRESS\n  Try:   POLYMARKET_SIGNATURE_TYPE=1 in .env -> restart')
            raise FatalBotError('Authentication failed')
        self.log.info('Auth: %s  |  Trader: %s', self.client.active_mode, self.client.trading_address)
        self._configure_runtime_state()
        await self._reconcile_saved_redemptions_before_position_barrier()
        if not self.cfg.dry_run and self.cfg.entry_mode == 'maker':
            if self.cfg.maker_gtd_ttl_s < 120.0:
                raise FatalBotError(f'LIVE maker: MAKER_GTD_TTL_S must be >= 120 (got {self.cfg.maker_gtd_ttl_s})')
            if not hasattr(OrderType, 'GTD'):
                raise FatalBotError('LIVE maker: OrderType.GTD missing from CLOB SDK â€” install py-clob-client-v2; refuse silent GTC')
            try:
                _probe = OrderArgs(token_id='0', price=0.5, size=1.0, side=_SDK_BUY, expiration=int(time.time()) + 240)
                if int(getattr(_probe, 'expiration', 0) or 0) <= 0:
                    raise FatalBotError('LIVE maker: OrderArgs.expiration not retained by SDK')
            except TypeError as e:
                raise FatalBotError('LIVE maker: OrderArgs lacks expiration= support â€” upgrade py-clob-client-v2') from e
            self.log.info('LIVE maker GTD gate OK  ttl=%ss  exp_formula=now+60+N', int(self.cfg.maker_gtd_ttl_s))
        balance_opt = await self.client.get_balance()
        if balance_opt is None:
            if self.cfg.dry_run:
                self.log.warning('CLOB balance fetch failed â€” dry-run continues with simulated bankroll floor')
                balance = self.cfg.min_order_size / max(self.cfg.max_bankroll_fraction, 1e-09)
            else:
                # K7 FIX: hold before the fatal exit so a Restart=always
                # supervisor cannot hammer the CLOB API in a ~5s crash loop.
                self.log.critical('LIVE trading refused: could not fetch USDC balance (API failure). Holding %.0fs before exit to avoid a supervisor crash loop.', FATAL_PREFLIGHT_HOLD_S)
                await asyncio.sleep(FATAL_PREFLIGHT_HOLD_S)
                raise FatalBotError('LIVE trading refused: could not fetch USDC balance (API failure â€” not the same as a $0 wallet)')
        else:
            balance = balance_opt
        self.log.info('CLOB balance: $%.4f', balance)
        if not self.cfg.dry_run and balance <= 0:
            # K7 FIX: hold before the fatal exit (see above).
            self.log.critical('LIVE trading refused: non-positive USDC balance. Holding %.0fs before exit to avoid a supervisor crash loop.', FATAL_PREFLIGHT_HOLD_S)
            await asyncio.sleep(FATAL_PREFLIGHT_HOLD_S)
            raise FatalBotError('LIVE trading refused: could not verify positive USDC balance')
        if balance < 1.0 and (not self.cfg.dry_run):
            self.log.warning('Low balance ($%.4f)', balance)
        _min_bankroll = self.cfg.min_order_size / max(self.cfg.max_bankroll_fraction, 1e-09)
        if balance * self.cfg.max_bankroll_fraction < self.cfg.min_order_size:
            if self.cfg.dry_run:
                self.log.warning('SIZING INERT: balance $%.4f * max_bankroll_fraction %.2f = $%.4f < min_order_size $%.2f.  Every Kelly stake will be 0.0 (skipped).  Fund to >= $%.2f (or raise max_bankroll_fraction) to size trades.', balance, self.cfg.max_bankroll_fraction, balance * self.cfg.max_bankroll_fraction, self.cfg.min_order_size, _min_bankroll)
            else:
                msg = 'REFUSING LIVE TRADE: balance $%.4f * max_bankroll_fraction %.2f = $%.4f < min_order_size $%.2f.  Cannot meet the venue minimum without violating the ruin-control cap.  Fund the account to >= $%.2f and restart.' % (balance, self.cfg.max_bankroll_fraction, balance * self.cfg.max_bankroll_fraction, self.cfg.min_order_size, _min_bankroll)
                self.log.critical(msg)
                # K7 FIX: hold before the fatal exit so a Restart=always
                # supervisor cannot hammer the CLOB API in a ~5s crash loop
                # while the account stays underfunded.
                await asyncio.sleep(FATAL_PREFLIGHT_HOLD_S)
                raise FatalBotError(msg)
        await self.recover_open_orders()
        if not self.cfg.dry_run:
            await self._verify_live_position_state()
        discovered_markets = await discover_5min_markets(self.cfg, self.session)
        if not discovered_markets:
            self.log.warning('No active 5-min markets found ? will poll for them')
        else:
            self.log.info('Found %d active 5/15-min crypto markets', len(discovered_markets))
        try:
            self.fivemin_markets = _merge_persisted_market_placeholders(discovered_markets, self._loaded_state)
        except RuntimeStateError as e:
            raise FatalBotError(f'Persisted market recovery failed: {e}') from e
        placeholder_count = sum(1 for m in self.fivemin_markets if getattr(m, '_recovery_placeholder', False))
        if placeholder_count:
            self.log.warning('Loaded %d persisted market placeholder(s); blocked from evaluation until rediscovered or settled on-chain', placeholder_count)
        self.markets = self.fivemin_markets
        for m in self.markets:
            is_placeholder = bool(getattr(m, '_recovery_placeholder', False))
            if not is_placeholder:
                self.polyfeed.subscribe(m.yes_token)
                self.polyfeed.subscribe(m.no_token)
            self.t2m[m.yes_token] = m
            self.t2m[m.no_token] = m
            self._5m_ids.add(m.market_id)
            if m.coin and not is_placeholder:
                self.by_coin.setdefault(m.coin, []).append(m)
        self.client.set_market_ref(self.t2m)
        self.userfeed = UserFeed(self.client, self.om)
        self.userfeed.set_markets(self.t2m)
        if self.cfg.dry_run:
            self.log.info('DRY_RUN: user fill feed disabled; real account fills will not mutate the paper ledger')
        else:
            self.userfeed.on_fill(self._on_fill)
        self.om.set_fill_replay_handler(self._replay_rest_fill)
        await self._seed_books()
        await self._enrich_market_fees([m for m in self.markets if not getattr(m, '_recovery_placeholder', False)])
        if self.cfg.dry_run:
            passed = True
            self.log.info('DRY_RUN â€” skipping signing test')
        elif not any(not getattr(m, '_recovery_placeholder', False) for m in self.markets):
            passed = True
        else:
            test_mkt = next(m for m in self.markets if not getattr(m, '_recovery_placeholder', False))
            test_token = test_mkt.yes_token
            test_tick = test_mkt.get_tick(test_token)
            test_neg = test_mkt.neg_risk
            self.log.info("Running signing test on '%s'â€¦", test_mkt.question[:40])
            passed = await self.client.test_order(test_token, test_tick, test_neg)
        if not passed:
            if not self.cfg.dry_run:
                self.log.warning('signing test FAILED for sig_type=%d â€” refusing to try alternatives in LIVE (each probe costs an order). Set POLYMARKET_SIGNATURE_TYPE=1 or 2 in .env and restart.', self.cfg.signature_type)
            else:
                self.log.warning('sig_type=%d failed â€” trying alternatives in DRY_RUNâ€¦', self.cfg.signature_type)
                original = self.cfg.signature_type
                for alt in [1, 0, 2]:
                    if alt == original:
                        continue
                    if await self.client._build_sdk(alt):
                        if await self.client.test_order(test_token, test_tick, test_neg):
                            self.log.info('sig_type=%d works! Set in .env to skip probe.', alt)
                            passed = True
                            break
        if not passed:
            self.log.critical("SIGNING FAILED â€” ALL SIG TYPES REJECTED\n  EOA: %s  Proxy: %s\n  If the reject was 'order_version_mismatch' you are on the\n  dead CLOB V1 SDK â€” install V2 (this is the usual cause):\n    1. %s/bin/pip install py-clob-client-v2\n    2. Wrap USDC.e -> pUSD (polymarket.com one-time approval)\n    3. Verify POLYMARKET_PROXY_ADDRESS + SIGNATURE_TYPE=2", self.client.signer_address, self.cfg.proxy_address or '(none)', sys.prefix)
            self.client.lib_broken = True
            raise FatalBotError('SIGNING FAILED â€” ALL SIG TYPES REJECTED')
        self.log.info('Signing test PASSED  sig_type=%d (%s)', self.cfg.signature_type, _SIG_LABELS.get(self.cfg.signature_type, '?'))
        self.log.info('=' * 68)
        self.log.info('  %-42s  %-6s  %-3s  %s', 'Question', 'Coin', 'NR', 'Tick(YES)')
        self.log.info('  ' + '-' * 66)
        for m in self.markets:
            self.log.info('  %-42s  %-6s  %-3s  %s', m.question[:42], m.coin or 'STABLE', 'Y' if m.neg_risk else 'N', m.tick_sizes.get(m.yes_token, '?'))
        self.log.info('=' * 68)
        # Chainlink is settlement oracle for 5m/15m crypto; Binance is leading wake-up only.
        self.tracker = PriceTracker(self.chainlink, self.cfg.prob_shrink, min_order_size_usdc=self.cfg.min_order_size, momentum_weight=self.cfg.momentum_weight)
        self._load_calibration_shrink()
        self.polyfeed.on_update(self._on_book)
        self.binance.on_update(self._on_price)
        self.chainlink.on_update(self._on_oracle_price)
        self.fivemin = FiveMinStrategy(self.cfg, self.om, self.risk, self.tracker, self.metrics)
        self.fivemin.polyfeed = self.polyfeed
        self.fivemin._market_lookup = lambda mid: next((m for m in self.markets if str(m.market_id) == str(mid)), None)
        self.fivemin._trade_pnl_in_flight_ref = self._trade_pnl_in_flight
        self.risk._bankroll_ref = lambda: self.fivemin.free_cash() if self.fivemin is not None else 0.0
        self.polyfeed.on_resolved(self._on_market_resolved)
        if balance_opt is not None or self.cfg.dry_run:
            self.fivemin.apply_authoritative_balance(balance)
        self.om.set_shadow_sink(self.fivemin._log_shadow)
        self.latency_arb = LatencyArb(self.cfg, self.om, self.tracker, self.polyfeed, self.by_coin)
        self.latency_arb.risk = self.risk
        self.latency_arb.strategy = self.fivemin
        self.fivemin.redeemer = self.redeemer
        _n_hold, _restored_mids, _state_problems = _restore_runtime_state(self.markets, self.fivemin, self.risk, self.redeemer, self.om, self.cfg.dry_run, self._loaded_state, self._trade_pnl_in_flight, self._applied_trade_order, self._applied_ioc_order)
        self._applied_trade_ids = set(self._applied_trade_order)
        self._applied_ioc_order_ids = set(self._applied_ioc_order)
        self.redeemer.on_state_change = self._save_runtime_state
        self.redeemer.on_fatal = lambda reason: self.risk._halt(f'redemption recovery: {reason}', halt_type='redemption')
        self.fivemin.on_state_change = self._save_runtime_state
        self.risk.on_state_change = self._save_runtime_state
        if _n_hold or _restored_mids:
            self.log.warning('Restored runtime state: markets=%d settlement_records=%d from %s', _n_hold, len(_restored_mids), self._state_path)
        if _state_problems:
            for problem in _state_problems:
                self.log.error('STATE RECOVERY: %s', problem)
            if not self.cfg.dry_run:
                raise FatalBotError('Live restart state is incomplete; refusing to trade')
        active_by_id = {str(m.market_id): m for m in self.markets}
        for _mid in _restored_mids:
            _m = active_by_id.get(str(_mid))
            # Expiry schedules an on-chain payout check; discovery absence alone is never resolution proof.
            if _m is not None and _m.end_time is not None and _m.end_time <= time.time():
                self.fivemin._settle_resolved_market(_mid)
        if not self.cfg.dry_run:
            _meta_values = list(self.fivemin._redeem_meta.values())
            _need_standard = any(not m.neg_risk for m in self.markets) or any(not bool(x.get('neg_risk')) for x in _meta_values)
            _need_neg = any(m.neg_risk for m in self.markets) or any(bool(x.get('neg_risk')) for x in _meta_values)
            _redeem_ok, _redeem_reasons = await asyncio.get_running_loop().run_in_executor(None, self.redeemer.preflight, _need_standard, _need_neg)
            if not _redeem_ok:
                for _reason in _redeem_reasons:
                    self.log.critical('REDEEM PREFLIGHT: %s', _reason)
                raise FatalBotError('Redemption preflight failed; refusing live trading')
        # Directional (bidirectional) GO/NO-GO gate removed together with the
        # strategy it authorised. LatArb keeps its own gates below.
        _mo_raw = re.sub('\\s+#.*$', '', os.environ.get('MEASURE_ONLY', '').strip()).lower()
        if _mo_raw and _mo_raw not in ('1', 'true', 'yes', 'y', 'on', '0', 'false', 'no', 'n', 'off'):
            raise FatalBotError(f'Invalid boolean env MEASURE_ONLY={_mo_raw!r}')
        _forced_measure_only = _mo_raw in ('1', 'true', 'yes', 'y', 'on')
        if _forced_measure_only:
            self.log.info('MEASURE-ONLY (forced via --measure-only): logging evals/outcomes, placing NO orders.')
        if self.cfg.latency_arb_enabled and (not self.cfg.dry_run) and self.cfg.require_latarb_proven_edge:
            ok_lat, lat_reasons = evaluate_latarb_go_no_go(self.cfg)
            if not ok_lat:
                # Strict live canary exception: allow unproven LatArb only when bootstrap
                # mode plus caps guarantee at most one venue-minimum FAK exposure.
                canary_cap = max(float(self.cfg.min_order_size), VENUE_MIN_ORDER_USDC)
                canary_ok = bool(getattr(self.cfg, 'latarb_bootstrap_live', False))
                canary_ok = canary_ok and float(self.cfg.max_order_size) <= canary_cap + 1e-09
                canary_ok = canary_ok and float(self.cfg.max_position) <= canary_cap + 0.75 + 1e-09
                canary_ok = canary_ok and int(self.cfg.max_open_orders) <= 1
                canary_ok = canary_ok and float(self.cfg.max_net_exposure_usdc) <= canary_cap + 0.75 + 1e-09
                canary_ok = canary_ok and float(self.cfg.max_gross_exposure_usdc) <= canary_cap + 1.25 + 1e-09
                if canary_ok:
                    self.log.warning('LATARB GO/NO-GO: BOOTSTRAP LIVE CANARY â€” shadow evidence failed/missing; allowing one min-size FAK only')
                    for rsn in lat_reasons:
                        self.log.warning('  - %s', rsn)
                else:
                    self.log.critical('LATARB GO/NO-GO: NO-GO â€” refusing live LatArb:')
                    for rsn in lat_reasons:
                        self.log.critical('  - %s', rsn)
                    raise FatalBotError('LATARB GO/NO-GO failed; live LatArb disabled until shadow evidence passes')
            else:
                self.log.info('LATARB GO/NO-GO: GO â€” strict shadow evidence passed')
        if self.cfg.latency_arb_enabled and (not self.cfg.dry_run) and getattr(self.cfg, 'require_latarb_live_proof', False):
            ok_live, live_reasons, live_stats = evaluate_latarb_live_proof(self.cfg)
            if not ok_live:
                self.log.critical('LATARB LIVE-PROOF: NO-GO â€” fill/settle evidence failed:')
                for rsn in live_reasons:
                    self.log.critical('  - %s', rsn)
                raise FatalBotError('LATARB LIVE-PROOF failed; disable REQUIRE_LATARB_LIVE_PROOF only for min-size bootstrap, then re-enable')
            mode = live_stats.get('mode', 'pass')
            if mode == 'bootstrap':
                self.log.warning('LATARB LIVE-PROOF: BOOTSTRAP â€” insufficient live samples; min-size only. fills=%s settle=%s', live_stats.get('fills'), live_stats.get('settle'))
            else:
                self.log.info('LATARB LIVE-PROOF: GO â€” fills+settle evidence passed %s', live_stats)
            # Seed the sizing flag from the boot verdict; refreshed thereafter by
            # _status_loop off the event loop (never inside _eval_market).
            self.latency_arb._live_proof_ok = mode != 'bootstrap'
        self.fivemin.measure_only = _forced_measure_only
        self.latency_arb._measure_only = _forced_measure_only
        loop = asyncio.get_running_loop()
        for sig_name in (signal.SIGINT, signal.SIGTERM):
            try:
                loop.add_signal_handler(sig_name, lambda: self.shutdown_ev.set())
            except NotImplementedError:
                pass
        self.running = True
        mode = 'DRY RUN' if self.cfg.dry_run else 'LIVE'
        arch = 'EVENT-DRIVEN' if self.cfg.event_driven else 'TIMER'
        self.log.info('Started [%s] [%s]  sig=%d  bal=$%.2f  mkts=%d  shards=%d  json=%s', mode, arch, self.cfg.signature_type, balance, len(self.markets), self.cfg.ws_shard_count, 'orjson' if _FAST_JSON else 'stdlib')
        self.tasks = [asyncio.create_task(self.polyfeed.run(), name='polyfeed'), asyncio.create_task(self.binance.run(), name='binance'), asyncio.create_task(self.chainlink.run(), name='chainlink'), asyncio.create_task(self._reconcile_loop(), name='reconcile'), asyncio.create_task(self._health_loop(), name='health'), asyncio.create_task(self._status_loop(), name='status'), asyncio.create_task(self._fivemin_refresh(), name='discovery'), asyncio.create_task(self.redeemer.run(), name='redeem'), asyncio.create_task(self._shutdown_wait(), name='shutdown')]
        if not self.cfg.dry_run:
            self.tasks.append(asyncio.create_task(self.userfeed.run(), name='userfeed'))
        if not self.cfg.event_driven:
            self.tasks.append(asyncio.create_task(self._fivemin_timer_loop(), name='fivemin_timer'))
        try:
            await asyncio.gather(*self.tasks)
        except asyncio.CancelledError:
            pass

    async def _seed_books(self) -> None:
        self.log.info('Seeding order books and tick sizesâ€¦')
        sem = asyncio.Semaphore(8)

        async def seed_book(tid: str) -> bool:
            async with sem:
                try:
                    async with self.session.get(f'{self.cfg.clob_url}/book', params={'token_id': tid}, timeout=aiohttp.ClientTimeout(total=6)) as r:
                        if not r.ok:
                            return False
                        d = await r.json(content_type=None)
                        bk = self.polyfeed.book(tid)
                        if not bk:
                            return False
                        bids = [(float(b['price']), float(b['size'])) for b in d.get('bids', []) if float(b.get('size', 0)) > 0]
                        asks = [(float(a['price']), float(a['size'])) for a in d.get('asks', []) if float(a.get('size', 0)) > 0]
                        bk.replace_snapshot(bids, asks)
                        bk.touch(time.monotonic(), allow_regression=True)
                        self.polyfeed._snapshot_received.add(tid)
                        m = self.t2m.get(tid)
                        if m:
                            if tid == m.yes_token:
                                m.book_yes = bk
                            else:
                                m.book_no = bk
                            # P1: market-specific ConditionalToken share minimum from book API
                            for _mk in ('min_order_size', 'minOrderSize', 'minimum_order_size'):
                                if d.get(_mk) is None:
                                    continue
                                try:
                                    mos = float(d[_mk])
                                    if mos > 0:
                                        if m.min_order_size is None or mos > float(m.min_order_size):
                                            m.min_order_size = mos
                                except Exception:
                                    pass
                                break
                        return True
                except Exception as e:
                    self.log.warning('Book seed %s: %s', tid[:12], e)
                    return False

        async def fetch_tick(tid: str) -> Optional[float]:
            async with sem:
                try:
                    async with self.session.get(f'{self.cfg.clob_url}/tick-size', params={'token_id': tid}, timeout=aiohttp.ClientTimeout(total=6)) as r:
                        if not r.ok:
                            return None
                        d = await r.json(content_type=None)
                        if isinstance(d, (int, float)):
                            raw = d
                        elif isinstance(d, str):
                            raw = d
                        elif isinstance(d, dict):
                            raw = d.get('minimum_tick_size') or d.get('tick_size') or d.get('minTickSize')
                        else:
                            raw = None
                        ts = float(raw) if raw else 0.0
                        if ts <= 0 or ts >= 1:
                            ts = 0.01
                        m = self.t2m.get(tid)
                        if m:
                            m.set_tick(tid, ts)
                        return ts
                except Exception as e:
                    self.log.warning('Tick-size %s: %s', tid[:12], e)
                    return None
        toks = [tid for tid, mkt in self.t2m.items() if not getattr(mkt, '_recovery_placeholder', False)]
        book_results, tick_results = await asyncio.gather(asyncio.gather(*[seed_book(t) for t in toks], return_exceptions=True), asyncio.gather(*[fetch_tick(t) for t in toks], return_exceptions=True))
        books_ok = sum((1 for r in book_results if r is True))
        tick_ok = sum((1 for r in tick_results if isinstance(r, float) and 0 < r < 1))
        self.log.info('Seeded %d/%d books, %d/%d ticks', books_ok, len(toks), tick_ok, len(toks))

    async def _enrich_market_fees(self, markets: List[Market]) -> None:
        """Fetch per-market feeRate + exponent from CLOB. Keeps CATEGORY_FEE_RATE as fallback."""
        if not markets or not self.client or not getattr(self.client, 'sdk', None):
            return
        loop = asyncio.get_running_loop()
        sdk = self.client.sdk
        seen: Set[str] = set()
        updated = 0

        def _fetch_one(cond: str, yes_tid: str) -> Tuple[Optional[float], bool, float]:
            rate: Optional[float] = None
            enabled = False
            exp = 1.0
            try:
                getter = getattr(sdk, 'get_clob_market_info', None)
                if getter and cond:
                    info = getter(cond)
                    fd = (info or {}).get('fd') or {}
                    r = fd.get('r')
                    e = fd.get('e')
                    if e is not None:
                        try:
                            exp = float(e) if float(e) > 0 else 1.0
                        except Exception:
                            exp = 1.0
                    if r is not None:
                        rf = float(r)
                        rate = rf if rf <= 1.0 else rf / 10000.0
                        enabled = rate > 0
                        return (rate, enabled, exp)
            except Exception:
                pass
            try:
                bps_fn = getattr(sdk, 'get_fee_rate_bps', None)
                if bps_fn and yes_tid:
                    bps = int(bps_fn(yes_tid) or 0)
                    if bps > 0:
                        rate = bps / 10000.0 if bps > 1 else float(bps)
                        enabled = rate > 0
                exp_fn = getattr(sdk, 'get_fee_exponent', None)
                if exp_fn and yes_tid:
                    try:
                        exp = float(exp_fn(yes_tid) or 1.0) or 1.0
                    except Exception:
                        pass
            except Exception:
                pass
            return (rate, enabled, exp)

        tasks = []
        mkts: List[Market] = []
        for m in markets:
            key = m.condition_id or m.market_id
            if not key or key in seen:
                continue
            seen.add(key)
            mkts.append(m)
            tasks.append(loop.run_in_executor(None, _fetch_one, m.condition_id or '', m.yes_token))
        if not tasks:
            return
        results = await asyncio.gather(*tasks, return_exceptions=True)
        for m, res in zip(mkts, results):
            if isinstance(res, Exception) or not isinstance(res, tuple):
                continue
            rate, enabled, exp = res[0], res[1], (res[2] if len(res) > 2 else 1.0)
            if rate is None:
                continue
            m.fee_rate = float(rate)
            m.fee_exponent = float(exp) if exp and float(exp) > 0 else 1.0
            m.fees_enabled = bool(enabled) or float(rate) > 0
            updated += 1
        if updated:
            self.log.info('Per-market fees: updated %d/%d markets (fallback CATEGORY_FEE_RATE=%.4f)', updated, len(mkts), self.cfg.category_fee_rate)

    async def _on_market_resolved(self, event: dict) -> None:
        if not self.running or not self.fivemin:
            return
        tid = event.get('asset_id') or ''
        mkt = self.t2m.get(tid) if tid else None
        if mkt is None:
            cond = str(event.get('condition_id') or event.get('conditionId') or '')
            if cond:
                for m in self.fivemin_markets:
                    if (m.condition_id or '') == cond:
                        mkt = m
                        break
        if mkt is None:
            self.log.debug('market_resolved: no local market for event %s', tid[:18] if tid else event.get('condition_id', '?'))
            return
        winning = str(event.get('winning_asset_id') or event.get('winningAssetId') or event.get('winning_outcome') or event.get('winner') or tid or '')
        self.log.info('market_resolved push %s â€” settling (winner=%s redeem=%s)', mkt.coin, (winning or '?')[:18], getattr(self.cfg, 'redeem_enabled', False))
        self.fivemin._settle_resolved_market(mkt.market_id, winning_asset_id=winning or None)

    async def _on_book(self, tid: str, book: OrderBook) -> None:
        m = self.t2m.get(tid)
        if not m or not self.running:
            return
        if self.client.lib_broken:
            return
        if tid == m.yes_token:
            m.book_yes = book
        else:
            m.book_no = book
        if self.risk.halted:
            if not self.shutdown_ev.is_set():
                if self.cfg.auto_flatten_on_halt:
                    try:
                        await self._flatten_all_positions()
                    except Exception as e:
                        self.log.error('auto_flatten_on_halt failed: %s', e)
                try:
                    await self.om.cancel_all()
                finally:
                    self.shutdown_ev.set()
            return
        if not self.risk.ok():
            return
        # Directional (bidirectional) evaluate_single fan-out removed: LatArb is
        # driven by _on_price / _on_oracle_price, not by book updates.

    async def _on_oracle_price(self, coin: str, price: float) -> None:
        """Chainlink ticks update PriceTracker via its own callback; also re-eval LatArb on oracle moves."""
        if not self.running or self.risk.halted:
            return
        if self.latency_arb:
            try:
                t = asyncio.create_task(self.latency_arb.on_binance_tick(coin, price, is_lead=False), name=f'latarb_cl_{coin}')
                self._bg_tasks.add(t)
                t.add_done_callback(self._bg_tasks.discard)
            except Exception as e:
                self.log.debug('LatencyArb oracle spawn error: %s', e)

    async def _on_price(self, coin: str, price: float) -> None:
        if not self.running or self.risk.halted:
            return
        if self.latency_arb:
            try:
                t = asyncio.create_task(self.latency_arb.on_binance_tick(coin, price, is_lead=True), name=f'latarb_{coin}')
                self._bg_tasks.add(t)
                t.add_done_callback(self._bg_tasks.discard)
            except Exception as e:
                self.log.debug('LatencyArb spawn error: %s', e)
        # Directional (bidirectional) evaluate_single fan-out removed.

    async def _on_fill(self, mkt: Market, tid: str, side_str: str, shares: float, price: float, trade_id: str='', order_ids: Optional[Set[str]]=None, aggregate_ioc: bool=False) -> bool:
        if not math.isfinite(price) or not 0.0 < price < 1.0:
            self.log.warning('_on_fill: invalid price %r for %s â€” dropping', price, tid[:12])
            return False
        if not math.isfinite(shares) or not 0.0 < shares < 100000000.0:
            self.log.warning('_on_fill: invalid shares %r for %s â€” dropping', shares, tid[:12])
            return False
        async with self._pos_lock:
            event_order_ids = {str(x) for x in (order_ids or set()) if x}
            already_applied = bool(trade_id and trade_id in self._applied_trade_ids) or bool(event_order_ids & self._applied_ioc_order_ids)
            if already_applied:
                # A prior in-memory apply whose write failed reaches this branch too;
                # retry the same complete snapshot before acknowledging the event.
                self._remember_applied_fill(trade_id)
                try:
                    self._save_runtime_state()
                except Exception as e:
                    self.om.latch_fill_failure(f'duplicate fill checkpoint failed for {trade_id or tid}: {e}')
                    raise
                return False
            if side_str not in ('BUY', 'SELL'):
                self.log.warning('_on_fill: unknown side %r â€” dropping', side_str)
                return
            side = Side.BUY if side_str == 'BUY' else Side.SELL
            pos = mkt.pos_yes if tid == mkt.yes_token else mkt.pos_no
            old_yes_cost = mkt.pos_yes.cost
            old_no_cost = mkt.pos_no.cost
            sell_fill = 0.0

            def _taker_fee(px: float, qty: float) -> float:
                fps = _market_fee_per_share(mkt, self.cfg, px)
                if fps > 0:
                    return fps * qty
                rate = self.cfg.category_fee_rate
                if rate > 0:
                    return _fee_per_share(rate, px, 1.0) * qty
                return self.cfg.taker_fee_bps * 0.0001 * px * qty
            entry_fee = 0.0
            if side == Side.BUY:
                entry_fee = _taker_fee(price, shares)
                pos.add(shares, price * shares + entry_fee)
                if self.fivemin:
                    _rk = (mkt.market_id, tid)
                    _filled_notional = price * shares + entry_fee
                    _rem = self.fivemin._pending_entry.get(_rk, 0.0) - _filled_notional
                    if _rem <= 1e-09:
                        self.fivemin._pending_entry.pop(_rk, None)
                    else:
                        self.fivemin._pending_entry[_rk] = _rem
                if self.fivemin:
                    _side_label = 'UP' if tid == mkt.yes_token else 'DN'
                    # F9: prefer OM entry tag (set at LatArb place), then volatile hold flags.
                    _tag = self.om.get_entry_strategy(tid) if self.om is not None else None
                    _is_latarb = _tag == 'latarb' or tid in getattr(mkt, 'latarb_hold_tokens', set()) or bool(getattr(mkt, 'latarb_hold', False))
                    if _is_latarb:
                        mkt.latarb_hold = True
                        if hasattr(mkt, 'latarb_hold_tokens'):
                            mkt.latarb_hold_tokens.add(tid)
                        if self.om is not None:
                            self.om.tag_entry_strategy(tid, 'latarb')
                        if self.latency_arb is not None:
                            self.latency_arb.record_realized_slip(tid, float(price))
                        # P0: settle/redeem meta on fill so market_resolved can recycle capital
                        try:
                            self.fivemin.register_latarb_fill_for_settle(mkt, tid, float(shares), float(price), float(entry_fee))
                        except Exception as _re:
                            self.log.warning('latarb settle meta register failed: %s', _re)
                    self.fivemin._calib_entry_meta[mkt.market_id, tid] = {'coin': mkt.coin, 'side': _side_label, 'strategy': 'latarb' if _is_latarb else 'directional', 'open_price': self.fivemin._open_prices.get(mkt.market_id, 0.0)}
                if self.metrics:
                    self.metrics.record_fill()
            elif pos.shares > 0:
                sell_fill = min(shares, pos.shares)
                avg_at_sell = pos.avg_price
                exit_fee = _taker_fee(price, sell_fill)
                partial_pnl = (price - avg_at_sell) * sell_fill - exit_fee
                flight_key = (mkt.market_id, tid)
                self._trade_pnl_in_flight[flight_key] = self._trade_pnl_in_flight.get(flight_key, 0.0) + partial_pnl
                pos.reduce(sell_fill)
                if self.fivemin and flight_key in self.fivemin._redeem_meta:
                    if pos.shares < 1e-06:
                        self.fivemin._redeem_meta.pop(flight_key, None)
                        self.fivemin._pending_redemptions.pop(flight_key, None)
                    else:
                        meta = self.fivemin._redeem_meta[flight_key]
                        meta['shares'] = float(pos.shares)
                        meta['cost'] = float(pos.cost)
                        meta['est_pnl'] = (1.0 - pos.avg_price) * pos.shares
                        self.fivemin._pending_redemptions[flight_key] = (pos.shares, pos.avg_price, 1.0)
                if self.fivemin and flight_key in self.fivemin._shares_in_flight:
                    self.fivemin._shares_in_flight[flight_key] = max(0.0, self.fivemin._shares_in_flight[flight_key] - sell_fill)
                    if self.fivemin._shares_in_flight[flight_key] < 1e-06:
                        self.fivemin._shares_in_flight.pop(flight_key, None)
                if self.metrics:
                    self.metrics.record_pnl(partial_pnl)
                if pos.shares < 1e-06:
                    net_pnl = self._trade_pnl_in_flight.pop(flight_key, partial_pnl)
                    self.risk.record_pnl(net_pnl)
                    self.risk.record_trade_closed(net_pnl)
                    if self.om is not None:
                        self.om.clear_entry_strategy(tid)
                    if hasattr(mkt, 'latarb_hold_tokens'):
                        mkt.latarb_hold_tokens.discard(tid)
                        if not mkt.latarb_hold_tokens:
                            mkt.latarb_hold = False
                    if self.fivemin:
                        self.fivemin._tp1_taken.pop(flight_key, None)
                        self.fivemin._entry_edges.pop(flight_key, None)
                        self.fivemin._shares_in_flight.pop(flight_key, None)
                        self.fivemin._fast_exit_counts.pop(flight_key, None)
                        self.fivemin.record_outcome(net_pnl > 0, market_id=mkt.market_id, net_pnl=float(net_pnl), coin=mkt.coin, side='UP' if tid == mkt.yes_token else 'DN', strategy=self.fivemin._calib_entry_meta.get((mkt.market_id, tid), {}).get('strategy', 'directional'), outcome_kind='trade_pnl', log_calibration=False)
                        if net_pnl < 0.0:
                            self.fivemin._realized_loss[mkt.market_id] = self.fivemin._realized_loss.get(mkt.market_id, 0.0) + net_pnl
                            _rl = self.fivemin._realized_loss[mkt.market_id]
                            if _rl <= -self.cfg.max_position:
                                self.log.warning('REALIZED-LOSS CAP: market %s now at $%.2f realized loss (max_position $%.2f).  New entries blocked until fully flat.', mkt.market_id[:12], _rl, self.cfg.max_position)
                        if mkt.pos_yes.shares < 1e-06 and mkt.pos_no.shares < 1e-06:
                            self.fivemin._realized_loss.pop(mkt.market_id, None)
                            if hasattr(mkt, 'latarb_hold_tokens'):
                                mkt.latarb_hold_tokens.clear()
                            mkt.latarb_hold = False
                            if self.om is not None:
                                self.om.clear_entry_strategy(mkt.yes_token)
                                self.om.clear_entry_strategy(mkt.no_token)
            if self.fivemin:
                new_yes_cost = mkt.pos_yes.cost
                new_no_cost = mkt.pos_no.cost
                delta = new_yes_cost - new_no_cost - (old_yes_cost - old_no_cost)
                self.fivemin._net_exposure += delta
                gross_delta = new_yes_cost + new_no_cost - (old_yes_cost + old_no_cost)
                self.fivemin._gross_exposure += gross_delta
                if side == Side.BUY:
                    self.fivemin._balance_cache = max(0.0, self.fivemin._balance_cache - (price * shares + entry_fee))
                    self.fivemin.note_cash_mutation()
                elif sell_fill > 0:
                    self.fivemin._balance_cache += price * sell_fill - _taker_fee(price, sell_fill)
                    self.fivemin.note_cash_mutation()
            self._remember_applied_fill(trade_id, event_order_ids if aggregate_ioc else set())
            try:
                self._save_runtime_state()
            except Exception as e:
                self.om.latch_fill_failure(f'fill apply checkpoint failed for {trade_id or tid}: {e}')
                raise
            probe_sz = shares if side == Side.BUY else sell_fill
            if probe_sz > 0 and self.om is not None:
                try:
                    self.om.spawn_fill_probe(tid, side, price, probe_sz, trade_id='')
                except Exception:
                    pass

            return True

    async def _replay_rest_fill(self, trade: dict) -> bool:
        trade_id = str(trade.get('trade_id') or trade.get('tradeId') or trade.get('id') or trade.get('transaction_hash') or '')
        if self.cfg.dry_run and not trade_id.startswith('dry-'):
            self.log.debug('DRY_RUN: ignoring live REST fill replay %s', trade_id[:16])
            return False
        if not trade_id:
            raise RuntimeStateError(f'fill payload has no durable trade id: {trade!r}')
        asset_id = str(trade.get('asset_id') or trade.get('token_id') or trade.get('tokenId') or '')
        if not asset_id:
            raise RuntimeStateError(f'fill {trade_id} has no asset_id')
        mkt = self.t2m.get(asset_id)
        if mkt is None:
            raise RuntimeStateError(f'fill {trade_id} references unknown token {asset_id}')
        side_raw = str(trade.get('side', '')).upper()
        if side_raw not in ('BUY', 'SELL'):
            raise RuntimeStateError(f'fill {trade_id} has invalid side {side_raw!r}')
        try:
            price = float(trade.get('price') or 0)
            size = float(trade.get('size') or trade.get('filled_size') or trade.get('maker_amount_filled') or trade.get('taker_amount_filled') or 0)
        except (TypeError, ValueError) as e:
            raise RuntimeStateError(f'fill {trade_id} has malformed price/size') from e
        if not math.isfinite(price) or not math.isfinite(size) or price <= 0 or size <= 0:
            raise RuntimeStateError(f'fill {trade_id} has invalid price={price!r} size={size!r}')
        order_ids = self.om._extract_trade_order_ids(trade)
        self.log.info('_replay_rest_fill: applying %s %s @ %.4f (%.4f shares) id=%s (mkt=%s)', side_raw, asset_id[:12], price, size, trade_id[:16], mkt.market_id[:8])
        return await self._on_fill(mkt, asset_id, side_raw, size, price, trade_id=trade_id, order_ids=order_ids, aggregate_ioc=bool(trade.get('_ioc_aggregate')))

    async def _check_position_drift(self) -> int:
        if not self.client.sdk:
            return 0
        if self.cfg.dry_run:
            return 0
        threshold = self.cfg.drift_halt_threshold_shares
        loop = asyncio.get_running_loop()
        n_workers = max(1, int(self.cfg.drift_check_concurrency))
        sem = asyncio.Semaphore(n_workers)
        io_pool = self._drift_io_pool
        tasks_meta: List[Tuple[Market, str, float, str]] = []
        for mkt in list(self.markets):
            for tid, pos, side_label in ((mkt.yes_token, mkt.pos_yes, 'YES'), (mkt.no_token, mkt.pos_no, 'NO')):
                tasks_meta.append((mkt, tid, pos.shares, side_label))
        if not tasks_meta:
            return 0

        async def _fetch_one(tid: str) -> float:
            async with sem:

                def _get_bal() -> float:
                    sdk = self.client.sdk
                    getter = getattr(sdk, 'get_balance_allowance', None)
                    if not getter or AssetType is None:
                        return float('nan')
                    try:
                        params = BalanceAllowanceParams(asset_type=AssetType.CONDITIONAL, token_id=tid)
                        resp = getter(params)
                        if isinstance(resp, dict):
                            raw = resp.get('balance') or resp.get('balance_allowance') or 0
                            return _parse_bal_micro(raw) / _USDC_SCALE
                    except Exception:
                        pass
                    return float('nan')
                try:
                    return await loop.run_in_executor(io_pool, _get_bal)
                except Exception:
                    return float('nan')
        results = await asyncio.gather(*(_fetch_one(meta[1]) for meta in tasks_meta), return_exceptions=False)
        drift_count = 0
        nan_count = 0
        first_msg = ''
        for (mkt, tid, local_shares, side_label), chain_shares in zip(tasks_meta, results):
            if not math.isfinite(chain_shares):
                nan_count += 1
                continue
            diff = abs(local_shares - chain_shares)
            if diff >= threshold:
                drift_count += 1
                direction = 'OVER' if local_shares > chain_shares else 'UNDER'
                msg = f'POSITION DRIFT mkt={mkt.market_id[:8]} {side_label} local={local_shares:.4f} chain={chain_shares:.4f} diff={diff:.4f} ({direction})'
                self.log.critical(msg)
                if not first_msg:
                    first_msg = msg
        if nan_count:
            self.log.warning('drift check: %d/%d fetches returned NaN â€” coverage may be incomplete; if this persists, on-chain RPC is down', nan_count, len(results))
        if nan_count == len(results) and len(results) > 0:
            self.risk._halt(f'drift check: total RPC failure â€” all {len(results)} fetches returned NaN', halt_type='rpc')
        if drift_count:
            self.risk._halt(f'position drift on {drift_count} market(s); first: {first_msg}', halt_type='drift')
        return drift_count

    @staticmethod
    def _is_owned_order(order: dict, trading_address: str) -> bool:
        if not isinstance(order, dict):
            return False
        maker = str(order.get('maker_address') or order.get('makerAddress') or order.get('owner') or '').lower()
        if not maker or maker in ('none', 'null'):
            return True
        if not maker.startswith('0x'):
            return True
        return maker == (trading_address or '').lower()

    async def recover_open_orders(self) -> None:
        if self.cfg.dry_run:
            self.log.info('DRY_RUN: skip open-order recovery barrier')
            return
        if not self.client.sdk:
            raise FatalBotError('recover_open_orders: no SDK â€” cannot verify open orders')
        try:
            remote = await self.client.list_open_orders()
        except Exception as e:
            raise FatalBotError(f'recover_open_orders: list_open_orders failed: {e}') from e
        trading = (self.client.trading_address or '').lower()
        owned = [o for o in remote if self._is_owned_order(o, trading)]
        if not owned:
            async with self.om._lock:
                self.om._orders.clear()
                self.om._by_token.clear()
            self.log.info('Open-order recovery: no remote open orders')
            return
        self.log.warning('Open-order recovery: cancelling %d remote open order(s)', len(owned))
        for order in owned:
            oid = str(order.get('id') or order.get('orderID') or order.get('order_id') or '')
            if not oid:
                raise FatalBotError(f'recover_open_orders: open order missing id: {order!r}')
            ok = await self.client.cancel(oid)
            if not ok:
                self.log.warning('recover_open_orders: cancel returned false for %s â€” will verify remaining list', oid[:16])
        try:
            await self.client.cancel_all()
        except Exception as e:
            self.log.warning('recover_open_orders: cancel_all: %s', e)
        try:
            remaining = await self.client.list_open_orders()
        except Exception as e:
            raise FatalBotError(f'recover_open_orders: re-list failed after cancel: {e}') from e
        still = [o for o in remaining if self._is_owned_order(o, trading)]
        if still:
            ids = [str(o.get('id') or o.get('orderID') or '?')[:12] for o in still[:5]]
            raise FatalBotError(f'Open-order recovery did not converge â€” {len(still)} still open (sample={ids}). Refuse to trade with unmanaged resting risk.')
        async with self.om._lock:
            self.om._orders.clear()
            self.om._by_token.clear()
        self.log.info('Open-order recovery: converged â€” book clean')

    async def _apply_balance_snapshot(self, new_bal: float, expected_gen: Optional[int]=None) -> None:
        if self.fivemin is None:
            return
        shock = False
        outcome = 'applied'
        old_bal = 0.0
        async with self._pos_lock:
            old_bal = self.fivemin._balance_cache
            shock, outcome = self.fivemin.apply_authoritative_balance(new_bal, expected_gen=expected_gen)
        if outcome == 'stale_discarded':
            return
        if abs(new_bal - old_bal) > 1.0 and (not shock):
            self.log.info('Balance refresh: $%.2f -> $%.2f (delta=%+.2f gen=%d)', old_bal, new_bal, new_bal - old_bal, self.fivemin._balance_gen)
        if not shock:
            return
        try:
            n = await self.om.cancel_open_buys()
            self.log.warning('capital_shock: cancelled %d resting BUY order(s); SELL exits preserved', n)
        except Exception as e:
            self.log.error('capital_shock cancel_open_buys failed: %s', e)
        _net_cap, _gross_cap = self.fivemin.exposure_caps()
        gross = self.fivemin._gross_exposure
        free = max(0.0, new_bal)
        if self.cfg.halt_on_capital_shock and (not self.cfg.dry_run) and (gross > _gross_cap + 1e-09 or free * self.cfg.max_bankroll_fraction < self.cfg.min_order_size):
            self.risk._halt(f'capital_shock: free=${free:.2f} gross=${gross:.2f} gross_cap=${_gross_cap:.2f} â€” operator must re-arm after inventory is reduced or capital restored', halt_type='capital_shock')
        else:
            self.log.warning('capital_shock handled: free=$%.2f gross=$%.2f caps net/gross=$%.2f/$%.2f â€” new entries sized to residual (cooldown %.0fs)', free, gross, _net_cap, _gross_cap, self.fivemin._capital_shock_cancel_cooldown_s)

    async def _status_loop(self) -> None:
        while self.running:
            await asyncio.sleep(60)
            # N1 FIX: a transient error (balance API blip, metrics hiccup) must not
            # kill the process; fatal state errors still propagate.
            try:
                s = self.risk.status()
                expected_gen = self.fivemin._balance_gen if self.fivemin is not None else None
                bal = await self.client.get_balance()
                if self.fivemin is not None and bal is not None:
                    await self._apply_balance_snapshot(bal, expected_gen=expected_gen)
                bal_disp = self.fivemin._balance_cache if self.fivemin is not None else bal if bal is not None else float('nan')
                trading = 'PAUSED:lib_broken' if self.client.lib_broken else f"HALTED:{s['reason']}" if s['halted'] else 'OK'
                metrics_str = ''
                if self.metrics:
                    ms = self.metrics.summary()
                    metrics_str = f"  lat_p50={ms['lat_p50_ms']:.0f}ms  lat_p95={ms['lat_p95_ms']:.0f}ms  fills={ms['fills']}"
                self.log.info('STATUS  pnl=$%.2f  day=$%.2f  orders=%d  bal=$%.2f  %s  consec=%d%s', s['pnl'], s['daily'], s['orders'], bal_disp, trading, s.get('consec_losses', 0), metrics_str)
                if self.fivemin:
                    try:
                        n_settle = self.fivemin.settle_expired_latarb(self.fivemin_markets, time.time())
                        if n_settle:
                            self.log.info('  LATARB settle_poll due=%d', n_settle)
                    except Exception as se:
                        self.log.debug('settle_expired_latarb status: %s', se)
                    self.log.info('  DIAG  guard_hits=%d  triggers=%d  open_prices=%d  traded=%d  bal_gen=%d  shock_cd=%s', self.fivemin._diag_guard_hits, self.fivemin._diag_trigger_calls, len(self.fivemin._open_prices), len(self.fivemin._traded), self.fivemin._balance_gen, self.fivemin.in_capital_shock_cooldown())
                if self.latency_arb is not None and (self.cfg.latency_arb_enabled or self.latency_arb.attempts > 0):
                    ls = self.latency_arb.fills_summary()
                    self.log.info('  LATARB fills attempts=%d fills=%d miss=%d rate=%.1f%% roll_n=%d roll_rate=%.1f%% avg_edge=%.3f avg_slip=%.1fbps measure_only=%s', ls['attempts'], ls['fills'], ls['misses'], 100.0 * ls['fill_rate'], ls.get('rolling_n', 0), 100.0 * ls.get('rolling_fill_rate', 0.0), ls['avg_edge'], ls['avg_slip_bps'], self.latency_arb._measure_only)
                    skip_summary = self.latency_arb.skip_summary()
                    if skip_summary:
                        self.log.info('  LATARB skips %s', skip_summary)
                    # Rolling kill / re-enable (LatArb-only).
                    self.latency_arb.maybe_update_kill_switch()
                    # Live-proof sizing gate: same 60s cadence as before, but the
                    # JSONL scan now runs in a worker thread instead of blocking
                    # the event loop from inside LatencyArb._eval_market.
                    if self.cfg.dry_run or not getattr(self.cfg, 'require_latarb_live_proof', False):
                        self.latency_arb._live_proof_ok = False
                    else:
                        try:
                            _ok_lp, _, _lp_stats = await asyncio.get_running_loop().run_in_executor(None, evaluate_latarb_live_proof, self.cfg)
                            self.latency_arb._live_proof_ok = bool(_ok_lp) and (_lp_stats or {}).get('mode', 'pass') != 'bootstrap'
                        except Exception as lpe:
                            self.latency_arb._live_proof_ok = False
                            self.log.debug('live-proof refresh failed: %s', lpe)

            except asyncio.CancelledError:
                raise
            except (FatalBotError, RuntimeStateError):
                raise
            except Exception as e:
                self.log.warning('status loop iteration error (non-fatal): %s', e)

    async def _reconcile_loop(self) -> None:
        await asyncio.sleep(25)
        base_interval = max(5.0, self.cfg.reconcile_fills_interval_s)
        fast_interval = 5.0
        drift_every_n_cycles = 10
        cycle = 0
        last_bal_refresh = time.monotonic()
        while self.running:
            cycle += 1
            if not self.cfg.dry_run:
                try:
                    await self.om.reconcile_fills()
                except Exception as e:
                    self.log.warning('reconcile_fills error: %s', e)
                try:
                    await self.om.reconcile()
                except Exception as e:
                    self.log.warning('Reconcile error: %s', e)
                now_mono = time.monotonic()
                force_bal = bool(self.fivemin is not None and getattr(self.fivemin, '_balance_force_refresh', False))
                if force_bal or now_mono - last_bal_refresh >= self.cfg.balance_refresh_s:
                    last_bal_refresh = now_mono
                    try:
                        expected_gen = self.fivemin._balance_gen if self.fivemin is not None else None
                        new_bal = await self.client.get_balance()
                        if new_bal is not None and self.fivemin is not None:
                            await self._apply_balance_snapshot(new_bal, expected_gen=expected_gen)
                    except Exception as e:
                        self.log.debug('Balance refresh failed: %s', e)
            if cycle % drift_every_n_cycles == 0 and (not self.cfg.dry_run):
                try:
                    await self._check_position_drift()
                except Exception as e:
                    self.log.warning('drift check error: %s', e)
            if self.userfeed:
                ws_up = self.userfeed.connected and self.userfeed.last_msg_age_s < 60.0
            else:
                ws_up = False
            interval = base_interval if ws_up else fast_interval
            await asyncio.sleep(interval)

    async def _health_loop(self) -> None:
        await asyncio.sleep(45)
        while self.running:
            # N1 FIX: guard feed-health checks; a failed restart attempt retries
            # next cycle instead of killing the process.
            try:
                shard_ages = self.polyfeed.shard_ages()
                for sid, age in shard_ages.items():
                    if age > 90:
                        self.log.warning('Shard %d stale (%.0fs) â€” restarting', sid, age)
                        await self.polyfeed.restart_shard(sid)
                overall_age = self.polyfeed.last_msg_age_s
                if overall_age > 120:
                    self.log.warning('ALL shards stale â€” full reconnect')
                    await self.polyfeed.stop()
                    t = asyncio.create_task(self.polyfeed.run(), name='polyfeed_restart')
                    self._bg_tasks.add(t)
                    t.add_done_callback(self._bg_tasks.discard)
                stale_binance = [c for c in self.cfg.coins if self.binance.price_age_s(c) > 15.0]
                if stale_binance:
                    self.log.warning('Binance feed stale for %s â€” reconnecting', ', '.join(stale_binance))
                    await self.binance.restart()
                stale_cl = [c for c in self.cfg.coins if self.chainlink.price_age_s(c) > 20.0]
                if stale_cl:
                    self.log.warning('Chainlink RTDS stale for %s â€” reconnecting', ', '.join(stale_cl))
                    await self.chainlink.restart()
                await asyncio.sleep(45)

            except asyncio.CancelledError:
                raise
            except (FatalBotError, RuntimeStateError):
                raise
            except Exception as e:
                self.log.warning('health loop iteration error (non-fatal): %s', e)
                await asyncio.sleep(45)

    async def _fivemin_timer_loop(self) -> None:
        interval = self.cfg.strategy_interval_s
        await asyncio.sleep(5)
        while self.running:
            await asyncio.sleep(interval)
            if not self.running or self.risk.halted or self.client.lib_broken:
                continue
            if self.fivemin and self.fivemin_markets:
                try:
                    # Independent of discovery: recycle LatArb capital when intervals close.
                    self.fivemin.settle_expired_latarb(self.fivemin_markets, time.time())
                    # evaluate_all() is now an exposure resync only (directional entry retired).
                    await self.fivemin.evaluate_all([m for m in self.fivemin_markets if not getattr(m, '_recovery_placeholder', False)])
                except Exception as e:
                    self.log.debug('Timer loop error: %s', e)

    async def _fivemin_refresh(self) -> None:
        await asyncio.sleep(8)
        while self.running:
            await asyncio.sleep(self.cfg.discovery_interval_s)
            if not self.running:
                break
            try:
                new_markets = await discover_5min_markets(self.cfg, self.session)
                existing_by_id = {str(m.market_id): m for m in self.fivemin_markets}
                added_tokens: List[str] = []
                added_mkts: List[Market] = []
                for fresh in new_markets:
                    existing = existing_by_id.get(str(fresh.market_id))
                    if existing is not None and getattr(existing, '_recovery_placeholder', False):
                        if str(existing.yes_token) != str(fresh.yes_token) or str(existing.no_token) != str(fresh.no_token):
                            raise RuntimeStateError(f'rediscovered token identity changed for persisted market {fresh.market_id}')
                        if existing.condition_id and fresh.condition_id and existing.condition_id.lower() != fresh.condition_id.lower():
                            raise RuntimeStateError(f'rediscovered condition identity changed for persisted market {fresh.market_id}')
                        # Preserve positions, cost, holds, and entry tags; refresh only venue metadata.
                        existing.question = fresh.question
                        existing.condition_id = fresh.condition_id or existing.condition_id
                        existing.end_time = fresh.end_time
                        existing.coin = fresh.coin
                        existing.tf_secs = fresh.tf_secs
                        existing.liquidity = fresh.liquidity
                        existing.volatility = fresh.volatility
                        existing.neg_risk = fresh.neg_risk
                        existing.fees_enabled = fresh.fees_enabled
                        existing.fee_rate = fresh.fee_rate
                        existing.fee_exponent = fresh.fee_exponent
                        existing.min_order_size = fresh.min_order_size
                        existing.tick_sizes.update(fresh.tick_sizes)
                        setattr(existing, '_recovery_placeholder', False)
                        if existing.coin and existing not in self.by_coin.setdefault(existing.coin, []):
                            self.by_coin[existing.coin].append(existing)
                        added_tokens.extend([existing.yes_token, existing.no_token])
                        added_mkts.append(existing)
                        self.log.warning('Rehydrated persisted market %s before feed subscription (YES=%.6f NO=%.6f)', existing.market_id[:18], existing.pos_yes.shares, existing.pos_no.shares)
                    elif existing is None:
                        if str(fresh.market_id) in self._loaded_state.get('markets', {}):
                            raise RuntimeStateError(f'persisted market {fresh.market_id} reached refresh without its required recovery placeholder')
                        self.fivemin_markets.append(fresh)
                        existing_by_id[str(fresh.market_id)] = fresh
                        self.t2m[fresh.yes_token] = fresh
                        self.t2m[fresh.no_token] = fresh
                        self._5m_ids.add(fresh.market_id)
                        if fresh.coin:
                            self.by_coin.setdefault(fresh.coin, []).append(fresh)
                        added_tokens.extend([fresh.yes_token, fresh.no_token])
                        added_mkts.append(fresh)
                self.markets = self.fivemin_markets
                if added_tokens:
                    await self.polyfeed.subscribe_live(added_tokens)
                    self.userfeed.set_markets(self.t2m)
                    try:
                        await self._enrich_market_fees(added_mkts)
                    except Exception as fe:
                        self.log.debug('fee enrich on discovery: %s', fe)
                    self.log.info('Activated %d new/rehydrated markets (%d total)', len(added_mkts), len(self.fivemin_markets))
                now = time.time()
                if self.fivemin:
                    self.fivemin.settle_expired_latarb(self.fivemin_markets, now)
                keep: List[Market] = []
                expired_tids: List[str] = []
                expired_count = 0
                for mkt in self.fivemin_markets:
                    has_inventory = mkt.pos_yes.shares > 1e-09 or mkt.pos_no.shares > 1e-09 or bool(mkt.latarb_hold_tokens)
                    has_settlement = bool(self.fivemin and any(k[0] == mkt.market_id for k in self.fivemin._redeem_meta))
                    has_partial = any(k[0] == mkt.market_id for k in self._trade_pnl_in_flight)
                    if mkt.end_time and mkt.end_time < now - 300 and not (has_inventory or has_settlement or has_partial):
                        self.t2m.pop(mkt.yes_token, None)
                        self.t2m.pop(mkt.no_token, None)
                        expired_tids.extend([mkt.yes_token, mkt.no_token])
                        expired_count += 1
                    else:
                        keep.append(mkt)
                if expired_count:
                    self.fivemin_markets = keep
                    self.markets = keep
                    await self.polyfeed.unsubscribe(expired_tids)
                    if self.fivemin:
                        self.fivemin.cleanup_expired(self.fivemin_markets)
                    self._prune_expired_bot_state({m.market_id for m in self.fivemin_markets})
                    self._save_runtime_state()
                    self.log.info('Removed %d flat expired markets, unsubscribed %d tokens', expired_count, len(expired_tids))
            except RuntimeStateError as e:
                self.log.critical('Discovery recovery safety failure: %s', e)
                self.risk._halt(f'discovery recovery safety failure: {e}', halt_type='state')
            except Exception as e:
                self.log.debug('Discovery refresh: %s', e)

    def _prune_expired_bot_state(self, active_mids: Set[str]) -> None:
        for k in [k for k in self._trade_pnl_in_flight if k[0] not in active_mids]:
            residual = self._trade_pnl_in_flight.pop(k, 0.0)
            if abs(residual) > 1e-09:
                self.risk.record_pnl(residual)
                self.log.info('PNL_DRAIN %s | booked orphaned TP1 partial $%.2f to Risk (leg held to expiry, never full-closed)', k[0][:18], residual)
        self._5m_ids.intersection_update(active_mids)
        for coin, mkts in list(self.by_coin.items()):
            kept = [m for m in mkts if m.market_id in active_mids]
            if kept:
                self.by_coin[coin] = kept
            else:
                self.by_coin.pop(coin, None)

    def _load_calibration_shrink(self) -> None:
        path = os.path.expanduser(self.cfg.calibration_log_path)
        if not os.path.exists(path):
            return
        try:
            matched = build_matched_samples(load_calibration_rows(path))
            coin_stats: Dict[str, List[Tuple[float, bool]]] = {}
            for m in matched:
                coin = str(m.get('coin') or '')
                ask = m.get('ask')
                win = m.get('win')
                if coin and ask is not None and (win is not None):
                    coin_stats.setdefault(coin, []).append((float(ask), bool(win)))
            for coin, samples in coin_stats.items():
                if len(samples) < 30:
                    continue
                hits = sum((1 for _, w in samples if w))
                hit_rate = hits / len(samples)
                mean_ask = sum((a for a, _ in samples)) / len(samples)
                if mean_ask <= 0.01:
                    continue
                shrink_k = max(0.5, min(1.5, hit_rate / mean_ask))
                self.tracker._per_coin_shrink[coin] = shrink_k
                self.log.info('CALIB_SHRINK %s: n=%d hit=%.3f ask=%.3f -> shrink=%.2f', coin, len(samples), hit_rate, mean_ask, shrink_k)
        except Exception as e:
            self.log.warning('Calibration shrink load failed: %s', e)

    async def _shutdown_wait(self) -> None:
        await self.shutdown_ev.wait()
        await self._shutdown()

    async def _flatten_all_positions(self) -> None:
        if self.cfg.dry_run:
            return
        flattened = 0
        for mkt in list(self.fivemin_markets):
            for token, pos, book in ((mkt.yes_token, mkt.pos_yes, mkt.book_yes), (mkt.no_token, mkt.pos_no, mkt.book_no)):
                if pos.shares <= 0 or book is None or book.best_bid is None:
                    continue
                try:
                    tick = mkt.get_tick(token) if hasattr(mkt, 'get_tick') else 0.01
                    sell_price = max(tick, book.best_bid)
                    notional = pos.shares * sell_price
                    if notional < self.cfg.min_order_size:
                        continue
                    await self.om.place(token, Side.SELL, sell_price, notional, Strategy.TEMPORAL, otype='FOK', neg_risk=mkt.neg_risk, tick_size=tick, quote_ts=book.ts if book else None, max_quote_age_ms=self.cfg.book_max_age_ms)
                    flattened += 1
                except Exception as e:
                    self.log.error('flatten %s/%s failed: %s', mkt.coin, token[:8], e)
        if flattened:
            self.log.warning('auto_flatten_on_halt: dispatched %d FOK exits', flattened)

    async def _shutdown(self) -> None:
        if not self.running:
            return
        self.running = False
        self.log.info('Shutting downâ€¦')
        await self.om.cancel_all()
        await self.polyfeed.stop()
        await self.binance.stop()
        await self.chainlink.stop()
        if self.userfeed:
            await self.userfeed.stop()
        self._save_runtime_state()
        if self.fivemin:
            self.fivemin.close_calibration_log()
        if self.latency_arb:
            self.latency_arb.close_shadow_log()
        for t in self.tasks:
            if t is not asyncio.current_task():
                t.cancel()
        if self.metrics:
            self.log.info('Final metrics: %s', self.metrics.summary())
        self._drift_io_pool.shutdown(wait=True, cancel_futures=True)
        self.log.info('Final status: %s', self.risk.status())

    def _banner(self) -> None:
        self.log.info('=' * 64)
        self.log.info('  POLYMARKET CRYPTO BOT %s â€” Antigravity Opus 4.6', _BOT_VERSION)
        self.log.info('=' * 64)
        if self.cfg.private_key:
            key_hash = hashlib.sha256(self.cfg.private_key.encode()).hexdigest()[:8]
            self.log.info('  KeyHash  : %sâ€¦  (sha256[:8] of POLYMARKET_PRIVATE_KEY)', key_hash)
        else:
            self.log.info('  KeyHash  : <not set>')
        self.log.info('  Proxy    : %s', self.cfg.proxy_address[:20] if self.cfg.proxy_address else '(none â€” EOA mode)')
        self.log.info('  SigType  : %d (%s)', self.cfg.signature_type, _SIG_LABELS.get(self.cfg.signature_type, '?'))
        self.log.info('  Coins    : %s', ', '.join(self.cfg.coins))
        self.log.info('  Size     : $%.0f-$%.0f  MaxPos: $%.0f', self.cfg.min_order_size, self.cfg.max_order_size, self.cfg.max_position)
        self.log.info('  DryRun   : %s  (fill_prob=%.0f%%  latency=%.0fms)', self.cfg.dry_run, self.cfg.dry_run_fill_prob * 100, self.cfg.dry_run_latency_ms)
        self.log.info('  Mode     : %s  |  Shards: %d  |  JSON: %s', 'EVENT' if self.cfg.event_driven else 'TIMER', self.cfg.ws_shard_count, 'orjson' if _FAST_JSON else 'stdlib')
        self.log.info('  AdaptKelly: %s  |  Metrics: %s', self.cfg.adaptive_kelly, self.cfg.metrics_enabled)
        self.log.info('  LatArb   : enabled=%s  shadow=%s  age=%.0f..%.0fms  edge=%.3f  min_prob=%.2f  proof=%s/%s', self.cfg.latency_arb_enabled, self.cfg.latarb_shadow, self.cfg.latarb_shadow_min_age_ms, self.cfg.latarb_shadow_max_age_ms, self.cfg.latency_arb_edge, self.cfg.latency_arb_min_prob, self.cfg.require_latarb_proven_edge, self.cfg.require_latarb_live_proof)
        self.log.info('  SDK      : %s  (py-clob-client-v2=%s)', 'yes' if _HAS_SDK else 'NO', _pkg_version('py-clob-client-v2'))
        self.log.info('=' * 64)

def _run_analyze(path: Optional[str]) -> None:
    cfg = Config.from_env()
    resolved = path or cfg.calibration_log_path
    rows = load_calibration_rows(resolved)
    report = calibration_report(rows)
    print_calibration_report(report, resolved)
    allowed, reasons = go_no_go(report, min_samples=cfg.min_proven_samples, min_edge=cfg.min_proven_edge, max_adverse_bps=cfg.max_adverse_bps)
    print(f"go/no-go verdict  : {('GO' if allowed else 'NO-GO')}")
    if not allowed:
        for rsn in reasons:
            print(f'  - {rsn}')
    print('')

def _latarb_pick_close(rs: List[Dict[str, Any]]) -> Tuple[float, float, float]:
    """F8: close = row nearest true expiry. Prefer ttc in [0, 5]s if any, else min ttc.
    Returns (close_spot, open_spot, residual_ttc_s). Residual >> 0 means early proxy."""
    if not rs:
        return (0.0, 0.0, 999.0)
    near = [r for r in rs if 0.0 <= float(r.get('ttc', 999)) <= 5.0]
    if near:
        best = max(near, key=lambda r: float(r.get('ts', 0.0)))
    else:
        best = min(rs, key=lambda r: float(r.get('ttc', 999)))
    return (float(best['spot']), float(best['open']), float(best['ttc']))

def evaluate_latarb_go_no_go(cfg: 'Config') -> Tuple[bool, List[str]]:
    path = os.path.expanduser(cfg.latarb_shadow_path)
    if not os.path.exists(path):
        return (False, [f'LatArb shadow CSV not found: {path}'])
    required = {'ts_unix', 'market_id', 'coin', 'ttc', 'spot_disp', 'up_side', 'spot_price', 'open_price', 'yes_ask', 'no_ask', 'yes_age_ms', 'no_age_ms', 'sigma_horizon', 'model_prob', 'entry_vwap', 'fee_per_share', 'edge', 'top_depth_usdc', 'entry_fillable'}
    rows: List[Dict[str, Any]] = []
    try:
        with open(path, encoding='utf-8') as fh:
            reader = csv.DictReader(fh)
            missing = sorted(required - set(reader.fieldnames or []))
            if missing:
                return (False, ['LatArb shadow schema is legacy/insufficient; missing ' + ', '.join(missing[:8]) + (' ...' if len(missing) > 8 else '')])
            for raw in reader:
                try:
                    oracle_raw = str(raw.get('oracle_sign_ok', '') or '').strip().lower()
                    oracle_sign_ok = True if not oracle_raw else oracle_raw in ('1', 'true', 'yes', 'y')
                    rows.append({'ts': float(raw['ts_unix']), 'mid': str(raw['market_id']), 'coin': raw['coin'], 'ttc': float(raw['ttc']), 'disp': float(raw['spot_disp']), 'spot': float(raw['spot_price']), 'open': float(raw['open_price']), 'yes_ask': float(raw['yes_ask']) if raw['yes_ask'] else 0.0, 'no_ask': float(raw['no_ask']) if raw['no_ask'] else 0.0, 'ya': float(raw['yes_age_ms']), 'na': float(raw['no_age_ms']), 'sigma_horizon': float(raw['sigma_horizon']), 'model_prob': float(raw['model_prob']), 'entry_vwap': float(raw['entry_vwap']) if raw['entry_vwap'] else 0.0, 'fee': float(raw['fee_per_share']), 'edge': float(raw['edge']), 'top_depth': float(raw['top_depth_usdc']), 'entry_fillable': str(raw['entry_fillable']).strip().lower() in ('1', 'true', 'yes'), 'sweep': float(raw['sweep_price']) if raw.get('sweep_price') else 0.0, 'oracle_sign_ok': oracle_sign_ok, 'mos': float(raw.get('mos') or 0.0), 'req_shares': float(raw.get('req_shares') or 0.0)})
                except (ValueError, TypeError, KeyError):
                    continue
    except OSError as e:
        return (False, [f'LatArb shadow CSV unreadable: {e}'])
    if not rows:
        return (False, ['LatArb shadow CSV has no parseable current-schema rows'])
    by_mid: Dict[str, List[Dict[str, Any]]] = {}
    for row in rows:
        by_mid.setdefault(row['mid'], []).append(row)
    closes: Dict[str, Tuple[float, float, float]] = {}
    for mid, rs_ in by_mid.items():
        closes[mid] = _latarb_pick_close(rs_)
    live_min_age = max(0.0, float(cfg.latarb_shadow_min_age_ms))
    # P1: live LatArb is one position per market â€” score first executable signal only
    # (cooldown re-fires are NOT independent trades).
    scored_mids: Set[str] = set()
    winners = losers = 0
    breakeven_sum = 0.0  # N10 FIX: accumulator for dynamic breakeven gate
    breakeven_n = 0
    pnl = 0.0
    per_coin: Dict[str, Dict[str, float]] = {}
    for row in sorted(rows, key=lambda x: x['ts']):
        if row['mid'] in scored_mids:
            continue
        if row['ttc'] < 30 or row['ttc'] > 285:
            continue
        up = row['disp'] > 0
        age = row['ya'] if up else row['na']
        if age < live_min_age:
            continue
        if cfg.latarb_shadow_max_age_ms > 0 and age > cfg.latarb_shadow_max_age_ms:
            continue
        # F7: live dual-book stale gate (both books older than LATARB_DUAL_BOOK_STALE_MS).
        if min(row['ya'], row['na']) > LATARB_DUAL_BOOK_STALE_MS:
            continue
        if not row.get('oracle_sign_ok', True):
            continue
        mos_val = float(row.get('mos') or 0.0)
        sweep_for_mos = float(row.get('sweep') or 0.0)
        if mos_val > 0.0 and sweep_for_mos > 0.0 and cfg.max_order_size / max(sweep_for_mos, 0.001) + 1e-12 < mos_val:
            continue
        ask = row['yes_ask'] if up else row['no_ask']
        if not ask or ask <= 0 or ask > 0.65:
            continue
        if row['sigma_horizon'] <= 0 or row['open'] <= 0 or row['spot'] <= 0:
            continue
        log_disp = math.log(row['spot'] / row['open'])
        if not math.isfinite(log_disp) or abs(log_disp) < 0.15 * row['sigma_horizon']:
            continue
        if cfg.latency_arb_min_prob > 0 and row['model_prob'] < cfg.latency_arb_min_prob:
            continue
        if not row['entry_fillable'] or row['entry_vwap'] <= 0:
            continue
        if row['top_depth'] < cfg.min_top_book_usdc:
            continue
        if row['edge'] <= -998.0:
            continue  # D5 FIX: skip sentinel rows (edge=-999 = uncomputable)
        if row['edge'] < cfg.latency_arb_edge:
            continue
        scored_mids.add(row['mid'])
        close_spot, open_spot, _res_ttc = closes.get(row['mid'], (row['spot'], row['open'], 999.0))
        # Mid-window close is not settlement â€” do not score as W/L (prevents false GO).
        if _res_ttc > 5.0:
            continue
        won = close_spot > open_spot if up else close_spot < open_spot
        # Prefer sweep cost when present (matches live FOK gate); else entry_vwap+fee.
        cin = row['sweep'] if row.get('sweep', 0.0) and row['sweep'] > 0 else row['entry_vwap']
        if cin <= 0:
            cin = row['entry_vwap']
        fee = row['fee']
        if row.get('sweep', 0.0) and row['sweep'] > 0 and cfg.category_fee_rate > 0:
            fee = cfg.category_fee_rate * cin * (1.0 - cin)
        breakeven_sum += (cin + fee)  # N10 FIX: accumulate cost basis for dynamic breakeven
        breakeven_n += 1
        share_pnl = 1.0 - cin - fee if won else -cin - fee
        pnl += share_pnl
        winners += 1 if won else 0
        losers += 0 if won else 1
        st = per_coin.setdefault(row['coin'].upper(), {'n': 0.0, 'w': 0.0, 'pnl': 0.0})
        st['n'] += 1.0
        st['w'] += 1.0 if won else 0.0
        st['pnl'] += share_pnl
    reasons: List[str] = []
    n = winners + losers
    if n < cfg.latarb_min_proven_signals:
        reasons.append(f'insufficient independent LatArb markets: {n} < required {cfg.latarb_min_proven_signals} (first-signal-per-market)')
    # N10 FIX: dynamic breakeven win-rate gate (replaces hardcoded latarb_min_win_rate)
    w_be = (breakeven_sum / breakeven_n + 0.01) if breakeven_n > 0 else cfg.latarb_min_win_rate
    win_rate = winners / n if n else None
    if win_rate is None:
        reasons.append('LatArb has no scorable near-expiry closes (residual_ttc>5 for all gated fires) or no gated signals')
    elif win_rate < w_be:  # N10 FIX: dynamic breakeven gate
        reasons.append(f'LatArb win rate {win_rate:.3f} < dynamic breakeven {w_be:.3f} (mean_cost + 0.01 margin)')
    if pnl <= cfg.latarb_min_total_pnl:
        reasons.append(f'LatArb total share-PnL {pnl:+.4f} <= required {cfg.latarb_min_total_pnl:+.4f}')
    # Per-coin: only HARD-fail coins that are fully sampled. Undersampled / missing
    # coins no longer block the whole stack (one cold coin must not kill proven ones).
    # Operator should remove persistently weak coins from COINS after live settle data.
    for coin in sorted({c.upper() for c in cfg.coins}):
        st = per_coin.get(coin)
        if not st:
            continue  # no samples yet â€” aggregate gate still protects live
        cn = int(st['n'])
        if cn < cfg.latarb_min_proven_signals:
            continue  # undersampled â€” do not fail global GO
        cw = st['w'] / st['n'] if st['n'] > 0 else 0.0
        cp = st['pnl']
        if cw < w_be:  # N10 FIX: dynamic breakeven gate (was hardcoded latarb_min_win_rate)
            reasons.append(f'LatArb coin {coin} win rate {cw:.3f} < required {w_be:.3f} (dynamic breakeven) (n={cn})')
        if cp <= cfg.latarb_min_total_pnl:
            reasons.append(f'LatArb coin {coin} share-PnL {cp:+.4f} <= required {cfg.latarb_min_total_pnl:+.4f} (n={cn})')
    return (not reasons, reasons)

def evaluate_latarb_live_proof(cfg: 'Config') -> Tuple[bool, List[str], dict]:
    """Live GO: require FOK fill-rate + settlement ledger EV (not shadow alone).
    Bootstrap mode allows insufficient samples with warning (min-size canary only)."""
    fills = _load_latarb_fills_stats(_latarb_fills_path(cfg))
    settle = _load_latarb_settle_stats(cfg)
    reasons: List[str] = []
    min_att = int(getattr(cfg, 'latarb_min_live_attempts', 50) or 50)
    min_fr = float(getattr(cfg, 'latarb_min_live_fill_rate', 0.4) or 0.4)
    min_sn = int(getattr(cfg, 'latarb_min_settle_samples', 20) or 20)
    min_sw = float(getattr(cfg, 'latarb_min_settle_win_rate', 0.52) or 0.52)
    min_sp = float(getattr(cfg, 'latarb_min_settle_pnl', 0.0) or 0.0)
    bootstrap = bool(getattr(cfg, 'latarb_bootstrap_live', True))
    # Live authorization uses LIVE samples only â€” never dry-run contamination.
    att = int(fills.get('live_attempts') or 0)
    # P1: notional fill ratio preferred over binary any-fill rate
    fr = float(fills.get('live_notional_fill_ratio') or fills.get('live_fill_rate') or 0.0)
    sn = int(settle.get('live_n') or 0)
    sw = float(settle.get('live_win_rate') or 0.0)
    sp = float(settle.get('live_pnl') or 0.0)
    stats = {'fills': fills, 'settle': settle, 'attempts_used': att, 'fill_rate_used': fr, 'settle_n_used': sn, 'settle_wr_used': sw, 'settle_pnl_used': sp, 'mode': 'pass'}
    insufficient = att < min_att or sn < min_sn
    if insufficient:
        if bootstrap:
            stats['mode'] = 'bootstrap'
            return (True, [f'bootstrap: live attempts {att}/{min_att}, live settle {sn}/{min_sn} â€” min-size canary only (dry excluded)'], stats)
        if att < min_att:
            reasons.append(f'insufficient live FAK attempts: {att} < required {min_att} (see {_latarb_fills_path(cfg)}; dry_run rows ignored)')
        if sn < min_sn:
            reasons.append(f'insufficient live settle samples: {sn} < required {min_sn} (see {_latarb_settle_path(cfg)}; dry_run rows ignored)')
        return (False, reasons, stats)
    if fr < min_fr:
        reasons.append(f'live fill rate {fr:.3f} < required {min_fr:.3f}')
    if sw < min_sw:
        reasons.append(f'live settle win rate {sw:.3f} < required {min_sw:.3f}')
    if sp <= min_sp:
        reasons.append(f'live settle total PnL {sp:+.4f} <= required {min_sp:+.4f}')
    if reasons:
        stats['mode'] = 'fail'
        return (False, reasons, stats)
    stats['mode'] = 'pass'
    return (True, [], stats)

def _run_latarb_analyze(path: Optional[str]) -> None:
    import csv as _csv
    cfg = Config.from_env()
    resolved = os.path.expanduser(path or cfg.latarb_shadow_path)
    if not os.path.exists(resolved):
        print(f'ERROR: shadow CSV not found: {resolved}')
        print('  Run the patched bot with LATARB_SHADOW=true to record it.')
        return
    print('\n=== Latarb Offline Harness (strict live-parity schema) ===')
    print(f'shadow CSV : {resolved}')
    live_min_age = max(0.0, float(cfg.latarb_shadow_min_age_ms))
    print(f'gate config: min_age={live_min_age:.0f}ms max_age={cfg.latarb_shadow_max_age_ms:.0f}ms ask_cap=0.65 min_prob={cfg.latency_arb_min_prob:.2f} edge>={cfg.latency_arb_edge:.3f} min_top_depth=${cfg.min_top_book_usdc:.2f} scoring=first-signal-per-market\n')
    required = {'ts_unix', 'market_id', 'coin', 'ttc', 'spot_disp', 'up_side', 'spot_price', 'open_price', 'yes_ask', 'no_ask', 'yes_age_ms', 'no_age_ms', 'sigma_per_sec', 'sigma_horizon', 'z', 'model_prob', 'entry_vwap', 'sweep_price', 'slippage', 'fee_per_share', 'edge', 'top_depth_usdc', 'entry_fillable'}
    raw = []
    with open(resolved, encoding='utf-8') as fh:
        reader = _csv.DictReader(fh)
        missing = sorted(required - set(reader.fieldnames or []))
        if missing:
            print('ERROR: legacy/insufficient LatArb shadow schema.')
            print('  Missing fields: ' + ', '.join(missing[:12]) + (' ...' if len(missing) > 12 else ''))
            print('  Regenerate the CSV with the patched bot; old top-of-book-only')
            print('  files cannot validate live depth/slippage/fill economics.')
            return
        for r in reader:
            try:
                raw.append({'ts': float(r['ts_unix']), 'mid': r['market_id'], 'coin': r['coin'], 'ttc': float(r['ttc']), 'disp': float(r['spot_disp']), 'up': r['up_side'], 'spot': float(r['spot_price']), 'open': float(r['open_price']), 'yes_ask': float(r['yes_ask']) if r['yes_ask'] else 0.0, 'no_ask': float(r['no_ask']) if r['no_ask'] else 0.0, 'ya': float(r['yes_age_ms']), 'na': float(r['no_age_ms']), 'sigma_horizon': float(r['sigma_horizon']), 'model_prob': float(r['model_prob']), 'entry_vwap': float(r['entry_vwap']) if r['entry_vwap'] else 0.0, 'fee': float(r['fee_per_share']), 'edge': float(r['edge']), 'top_depth': float(r['top_depth_usdc']), 'entry_fillable': str(r['entry_fillable']).strip().lower() in ('1', 'true', 'yes'), 'sweep': float(r['sweep_price']) if r.get('sweep_price') else 0.0})
            except (ValueError, TypeError, KeyError):
                continue
    print(f'loaded rows: {len(raw):,}')
    if not raw:
        print('No parseable rows â€” nothing to analyze.')
        return
    mkt_close: Dict[str, Tuple[float, float, float]] = {}
    mkt_rows: Dict[str, List] = {}
    for r in raw:
        mkt_rows.setdefault(r['mid'], []).append(r)
    early_n = 0
    for mid, rs in mkt_rows.items():
        mkt_close[mid] = _latarb_pick_close(rs)
        if mkt_close[mid][2] > 5.0:
            early_n += 1
    print(f'close proxy : prefer ttc<=5s else min-ttc; markets with residual_ttc>5s: {early_n}/{len(mkt_close)}')
    print(f'independence: score first executable signal per market only (live one-position rule); unique markets in file={len(mkt_rows)}')
    min_age = live_min_age
    max_age = cfg.latarb_shadow_max_age_ms
    min_prob = cfg.latency_arb_min_prob
    edge_thr = cfg.latency_arb_edge
    stage = {'total': 0, 'entry_window': 0, 'age_ge_min': 0, 'age_le_max': 0, 'dual_book_ok': 0, 'ask_le65': 0, 'disp_ge_min': 0, 'prob_ge_min': 0, 'entry_fillable': 0, 'depth_ge_min': 0, 'edge_ge_thr': 0, 'first_per_market': 0}
    winners = losers = 0
    pnl = 0.0
    per_coin_pnl: Dict[str, float] = {}
    edge_hist: List[float] = []
    scored_mids: Set[str] = set()
    for r in sorted(raw, key=lambda x: x['ts']):
        stage['total'] += 1
        if r['mid'] in scored_mids:
            continue
        if r['ttc'] < 30 or r['ttc'] > 285:
            continue
        stage['entry_window'] += 1
        up = r['disp'] > 0
        book_age = r['ya'] if up else r['na']
        if book_age < min_age:
            continue
        stage['age_ge_min'] += 1
        if max_age > 0 and book_age > max_age:
            continue
        stage['age_le_max'] += 1
        # F7: match live dual-book stale gate
        if min(r['ya'], r['na']) > LATARB_DUAL_BOOK_STALE_MS:
            continue
        stage['dual_book_ok'] += 1
        ask = r['yes_ask'] if up else r['no_ask']
        if not ask or ask <= 0 or ask > 0.65:
            continue
        stage['ask_le65'] += 1
        if r['sigma_horizon'] <= 0:
            continue
        log_disp = math.log(r['spot'] / r['open']) if r['open'] > 0 else 0.0
        if not math.isfinite(log_disp):
            continue
        if abs(log_disp) < 0.15 * r['sigma_horizon']:
            continue
        stage['disp_ge_min'] += 1
        if min_prob > 0 and r['model_prob'] < min_prob:
            continue
        stage['prob_ge_min'] += 1
        if not r['entry_fillable'] or r['entry_vwap'] <= 0:
            continue
        stage['entry_fillable'] += 1
        if r['top_depth'] < cfg.min_top_book_usdc:
            continue
        stage['depth_ge_min'] += 1
        if r['edge'] < edge_thr:
            continue
        stage['edge_ge_thr'] += 1
        scored_mids.add(r['mid'])
        stage['first_per_market'] += 1
        close_spot, open_spot, _res_ttc = mkt_close.get(r['mid'], (r['spot'], r['open'], 999.0))
        # Mid-window close is not settlement â€” exclude from W/L (prevents false GO).
        if _res_ttc > 5.0:
            continue
        stage['close_ttc_ok'] = stage.get('close_ttc_ok', 0) + 1
        won = close_spot > open_spot if up else close_spot < open_spot
        cin = r['sweep'] if r.get('sweep', 0.0) and r['sweep'] > 0 else r['entry_vwap']
        if cin <= 0:
            cin = r['entry_vwap']
        fee = r['fee']
        if r.get('sweep', 0.0) and r['sweep'] > 0 and cfg.category_fee_rate > 0:
            fee = cfg.category_fee_rate * cin * (1.0 - cin)
        share_pnl = 1.0 - cin - fee if won else -cin - fee
        pnl += share_pnl
        per_coin_pnl[r['coin']] = per_coin_pnl.get(r['coin'], 0.0) + share_pnl
        winners += 1 if won else 0
        losers += 0 if won else 1
        edge_hist.append(r['edge'])
    if 'close_ttc_ok' not in stage:
        stage['close_ttc_ok'] = 0
    print('\nGate funnel:')
    prev = None
    for k, v in stage.items():
        if prev is None:
            print(f'  {k:16s}: {v:8,d}')
        else:
            pct = 100.0 * v / prev if prev else 0.0
            print(f'  {k:16s}: {v:8,d}  ({pct:5.1f}% of prior)')
        prev = v
    n_sig = winners + losers
    if n_sig:
        wr = 100.0 * winners / n_sig
        avg_edge = sum(edge_hist) / len(edge_hist) if edge_hist else 0.0
        print(f'\nSignals       : {n_sig:,}')
        print(f'Win rate      : {wr:.1f}%  ({winners}W / {losers}L)')
        print(f'PnL/share sum : {pnl:+.2f}')
        print(f'Avg gated edge: {avg_edge:+.4f}')
        if per_coin_pnl:
            print('Per-coin PnL  : ' + ', '.join((f'{c}={v:+.2f}' for c, v in sorted(per_coin_pnl.items()))))
        verdict = 'POSITIVE' if pnl > 0 and wr > 50 else 'NEGATIVE'
        print(f'\n>>> STRICT REALIZED-EDGE VERDICT: {verdict} ({pnl:+.2f} share-PnL units)')
    else:
        print('\nNo scorable signals (gates empty or all closes residual_ttc>5s â€” not a POSITIVE).')
    old_shadow_path = cfg.latarb_shadow_path
    cfg.latarb_shadow_path = resolved
    try:
        ok_gate, gate_reasons = evaluate_latarb_go_no_go(cfg)
    finally:
        cfg.latarb_shadow_path = old_shadow_path
    print(f"\n>>> LIVE LATARB PROOF GATE: {('GO' if ok_gate else 'NO-GO')}")
    if not ok_gate:
        for rsn in gate_reasons[:12]:
            print(f'  - {rsn}')
        if len(gate_reasons) > 12:
            print(f'  - ... {len(gate_reasons) - 12} more')
    print('\nCAVEAT: still not live-capital proof. Shadow quotes + spot-close proxy.')
    print(f'Requires real FOK fill rate (see {_latarb_fills_path(cfg)}), slippage,')
    print('and venue settlement from min-size live probes before sizing up.')
    ok_live, live_reasons, live_stats = evaluate_latarb_live_proof(cfg)
    print(f"\n>>> LIVE PROOF GATE: {('GO' if ok_live else 'NO-GO')} mode={live_stats.get('mode')}")
    print(f"  FOK attempts={live_stats.get('attempts_used')} fill_rate={live_stats.get('fill_rate_used'):.3f}")
    print(f"  settle n={live_stats.get('settle_n_used')} wr={live_stats.get('settle_wr_used'):.3f} pnl={live_stats.get('settle_pnl_used'):+.4f}")
    if not ok_live:
        for rsn in live_reasons[:8]:
            print(f'  - {rsn}')
    print('')

def main() -> None:
    parser = argparse.ArgumentParser(prog='polybot', description='Polymarket 5-min trading bot')
    parser.add_argument('--analyze', nargs='?', const='', metavar='CALIBRATION_CSV', help='Offline: print the calibration report + go/no-go verdict over the given calibration CSV (defaults to CALIBRATION_LOG_PATH) and exit. Does NOT trade or require credentials.')
    parser.add_argument('--latarb-analyze', nargs='?', const='', metavar='LATARB_SHADOW_CSV', help='Offline: replay the latency-arb gate over the recorded shadow CSV (defaults to LATARB_SHADOW_PATH) and measure REALIZED edge net of cost, then exit. Does NOT trade or require credentials. Faithfully replays sigma/model_prob/edge/age gates; book DEPTH is flagged unmeasurable (signal count is an upper bound).')
    parser.add_argument('--measure-only', action='store_true', help='Online: connect to all feeds, log every EVAL snapshot and OUTCOME to the calibration CSV, but place NO orders.  Forces the strategy into MEASURE-ONLY mode (every entry is a no-op)   Safe way to accumulate data without risking capital.')
    args = parser.parse_args()
    if args.analyze is not None:
        _run_analyze(args.analyze or None)
        return
    if getattr(args, 'latarb_analyze', None) is not None:
        _run_latarb_analyze(args.latarb_analyze or None)
        return
    if args.measure_only:
        os.environ['MEASURE_ONLY'] = '1'
    try:
        import uvloop
        uvloop.install()
        log.info('uvloop active (libuv event loop)')
    except ImportError:
        log.info('uvloop not installed â€” using stdlib asyncio loop')
    cfg = Config.from_env()
    errs = cfg.validate()
    if errs:
        for e in errs:
            print(f'ERROR: {e}')
        sys.exit(1)
    global _PROCESS_INSTANCE_LOCK
    try:
        _PROCESS_INSTANCE_LOCK = acquire_instance_lock(cfg)
    except FatalBotError as e:
        logging.getLogger('Bot').critical('%s', e)
        sys.exit(1)
    if cfg.proxy_address:
        log.info('Proxy  : %s', cfg.proxy_address)
    else:
        log.info('Proxy  : (none â€” EOA mode)')
    log.info('SigType: %d (%s)', cfg.signature_type, _SIG_LABELS.get(cfg.signature_type, '?'))
    try:
        asyncio.run(Bot(cfg).run())
    except KeyboardInterrupt:
        print('\nStopped.')
    except Exception as e:
        logging.getLogger('Bot').critical('Fatal: %s', e, exc_info=True)
        sys.exit(1)
if __name__ == '__main__':
    main()
