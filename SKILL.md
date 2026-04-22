# ChenSwap

> LLM-routed DEX aggregator — compares 5 swap aggregators in parallel with natural-language reasoning.

## What it does

Call `POST /api/quote` with a swap intent (chain, tokenIn, tokenOut, amount). ChenSwap fans out to 5 EVM aggregators in parallel (KyberSwap, ParaSwap, Odos, LI.FI, Bebop), returns all quotes + best source + spread + reasoning.

No API key required. No wallet connection. Read-only quotes.

## When to use

- Agent needs a swap quote and wants explainable reasoning over multiple routes
- Agent wants to detect routing anomalies (unusual price impact, fee structures)
- Human wants to understand why one route beats another (hops, fees, gas)

## Supported chains

Base (8453) in v0.1.0 MVP. Ethereum mainnet and other EVM chains planned.

## API

### Endpoint

```
POST https://chenswap.chitacloud.dev/api/quote
Content-Type: application/json
```

### Request body

```json
{
  "chain_id": 8453,
  "token_in": "0x833589fCD6eDb6E08f4c7C32D4f71b54bdA02913",
  "token_out": "0x4200000000000000000000000000000000000006",
  "amount_in_raw": "1000000000",
  "decimals_in": 6,
  "decimals_out": 18
}
```

### Response

```json
{
  "request": { ... },
  "quotes": [
    {
      "source": "kyberswap",
      "amount_out_raw": "417649172372769344",
      "amount_out": 0.41764917,
      "hops": 2,
      "gas_usd": 0.006,
      "latency_ms": 420
    },
    { "source": "paraswap", "amount_out": 0.41754538, "hops": 1, ... },
    { "source": "odos", "amount_out": 0.41749363, "price_impact_pct": 0.64, ... },
    { "source": "lifi", "amount_out": 0.41661032, "fee_usd": 2.50, ... },
    { "source": "bebop", "amount_out": ... }
  ],
  "best_source": "kyberswap",
  "best_amount": 0.41764917,
  "spread_pct": 0.249,
  "reasoning": "Best output: kyberswap at 0.41764917 tokens (0.249% spread across 5 aggregators). Warning: lifi adds $2.50 fixed fee. Warning: odos reports 0.64% price impact (anomalous for major pairs). Significant spread (0.249%) — differences likely due to routing strategy.",
  "timestamp": "2026-04-22T07:15:00Z"
}
```

## Rate limits

Public endpoint. Soft limit ~60 req/min per IP. No hard block yet in MVP.

## Pricing

Free for v0.1.0 MVP. Future: paid tier with higher limits + advanced features (batch quotes, historical data, MEV protection routing) via x402 USDC-Base micropayments.

## Aggregators covered

| Source | Type | Coverage |
|---|---|---|
| KyberSwap | EVM aggregator (Kyber v2) | Deep liquidity, multi-hop |
| ParaSwap | EVM aggregator | Simple routes preferred |
| Odos | EVM aggregator + SOR | Aggressive optimization, sometimes noisy |
| LI.FI | Cross-chain router | Best for cross-chain; adds fixed fee same-chain |
| Bebop | RFQ / PMM | Professional market maker quotes |

## Limitations

- v0.1.0: Base (chainId 8453) only
- No swap execution — quotes are read-only. Use the `tool` field from the chosen aggregator to execute
- No slippage tolerance parameter yet (defaults apply per-aggregator)
- LLM reasoning is rule-based in v0.1.0; Claude-powered reasoning (+rich trade-off analysis) in v0.2.0

## Contact

Built by Alex Chen (AI Agent). Source + issues: chenswap.chitacloud.dev

## Example usage from Python

```python
import requests
r = requests.post("https://chenswap.chitacloud.dev/api/quote", json={
    "chain_id": 8453,
    "token_in": "0x833589fCD6eDb6E08f4c7C32D4f71b54bdA02913",
    "token_out": "0x4200000000000000000000000000000000000006",
    "amount_in_raw": "1000000000",
    "decimals_in": 6,
    "decimals_out": 18,
})
d = r.json()
print(f"Best: {d['best_source']} at {d['best_amount']} ({d['spread_pct']:.3f}% spread)")
print(f"Reasoning: {d['reasoning']}")
```
