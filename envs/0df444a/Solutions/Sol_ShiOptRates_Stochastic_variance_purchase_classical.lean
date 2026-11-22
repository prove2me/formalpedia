-- Prove2me | solution 1 for ShiOptRates.Stochastic.variance_purchase_classical
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-08T22:45:15.817346+00:00
-- url     : https://prove2.me/submissions/6928d8b4-c16f-47e8-b989-93fa46d76ff9

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/Stochastic/VariancePurchase.lean
Original work Copyright (c) 2026 Yueheng Shi, released under the Apache License,
Version 2.0.  The original copyright and author notices are retained below.

MODIFICATIONS made for publication on Prove2me: declarations not reachable from
the published targets were removed by declaration-graph skeleton subtraction;
project imports were rewritten to platform `Definitions.Def_*` / `Theorems.Thm_*`
modules; the root namespace `OptRates` was renamed to `ShiOptRates`; the enclosing `namespace` is replaced by `section`+`open` and the target
theorem is renamed to `solution`; 
no statement or proof was otherwise altered.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiOptrates_Cost
import Definitions.Def_ShiOptrates_FunctionClass
import Definitions.Def_ShiOptrates_Stochastic_Bridge
import Definitions.Def_ShiOptrates_Stochastic_Recursion
import Definitions.Def_ShiOptrates_Stochastic_VariancePurchase
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Martingale.Basic



/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yueheng Shi
-/

/-!
# The mechanism: buying variance, and why the cost exponent decides everything

`Stochastic.sgd_rate` needs `K ≥ 8 L Δ₀ σ̂² / ε⁴` iterations from an oracle whose variance
is `σ̂²`.  But `σ̂` is not given by nature — it is *purchased*.  An oracle that averages
samples, or a quantum mean estimator, delivers variance `σ̂²` at a price
`price(σ̂) = a / σ̂ ^ p`, and `p` is the whole story:

| `p` | estimator | total queries |
|---|---|---|
| `2` | classical averaging, `a = L²` | `8 a L Δ₀ / ε⁴` — **independent of `σ̂`** |
| `1` | quantum mean estimation, `a ≍ L√d` | `8 a L Δ₀ σ̂ / ε⁴` — **strictly decreasing in `σ̂`** |

At `p = 2` the `σ̂²` in the iteration count cancels the `σ̂⁻²` in the price exactly, so
buying variance reduction is *cost-neutral*: this is the formal reason a classical sampler
cannot improve SGD's `ε⁻⁴` by averaging harder.  At `p = 1` the cancellation is incomplete
and the purchase is strictly profitable.  That broken tie is the mechanism behind every
quantum stochastic-optimization speedup in the literature.

This is the library's central abstraction discharged at L3: the classical and quantum
analyses share the oracle contract (*unbiased, variance `σ̂²`*) and the entire rate
analysis, and differ in one natural number.

Note which contract appears here: **unbiased**, not bounded-error.  Sidford–Zhang
(arXiv:2308.01582) make exactly this choice, debiasing the quantum estimator by MLMC
before using it, because — in their words — its bias "hinders its combination with various
optimization algorithms assuming unbiased inputs".  `Stochastic.accumulation_linear_tight`
is the machine-checked form of that obstruction.

## Main results

* `variance_purchase_total` — the total query bill as a function of `σ̂` and `p`.
* `variance_purchase_classical` — at `p = 2` the bill does not depend on `σ̂`.
* `variance_purchase_quantum` — at `p = 1` it is linear in `σ̂`.
* `variance_purchase_strict_gain` — hence strictly profitable to reduce `σ̂` when `p = 1`
  and exactly neutral when `p = 2`.
-/

section
open ShiOptRates
open ShiOptRates.Stochastic

open CostModel

/-- The bill, with the `σ̂` dependence isolated. -/
theorem variance_purchase_total (a L Δ ε σhat : ℝ) (p : ℕ) (ha : 0 ≤ a) :
    variancePurchaseTotal a L Δ ε σhat p ha
      = 8 * a * L * Δ * σhat ^ 2 / (σhat ^ p * ε ^ 4) := by
  simp only [variancePurchaseTotal, sgdIterations, powerCost]
  ring

theorem solution (a L Δ ε σhat : ℝ) (ha : 0 ≤ a) (hσ : σhat ≠ 0) :
    variancePurchaseTotal a L Δ ε σhat 2 ha = 8 * a * L * Δ / ε ^ 4 := by
  rw [variance_purchase_total]
  field_simp

/-! ### Calibration: Q-SGD

Buying variance below `ε` is wasted — the iteration count `8LΔ₀σ̂²/ε⁴` drops below one — so
the purchase stops at `σ̂ ≍ ε`.  Evaluating the bill there recovers the two published
bounded-variance rates. -/

end
