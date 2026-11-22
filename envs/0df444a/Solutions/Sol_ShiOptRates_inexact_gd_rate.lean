-- Prove2me | solution 1 for ShiOptRates.inexact_gd_rate
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-08T23:08:54.656199+00:00
-- url     : https://prove2.me/submissions/c2e0f15d-51f2-4b98-86c3-929c1eca50c0

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/Calibration.lean
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
import Theorems.Thm_ShiOptRates_exists_grad_le_of_const_schedule
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability



/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yueheng Shi
-/

/-!
# §5 — Calibration theorems

The library's evidence: named rates, stated with explicit constants, each obtained by
instantiating the *same* L1/L2 theorems at a different oracle contract and cost model.

| theorem | layer | rate |
|---|---|---|
| `gd_exact_rate` | L1 | `K ≥ 2LΔ₀/ε²` gradient evaluations |
| `inexact_gd_rate` | L1 | `K ≥ 4LΔ₀/ε²` iterations at accuracy `ε/√2` |
| `minibatch_query_count` | L1 | `≍ 8 L Δ₀ σ² / ε⁴` samples |
| `quantum_query_count` | L1+L2 | `≍ 4√2 · L Δ₀ σ √dim log(K/η) / ε³` queries |

The classical `ε⁻⁴` and the quantum `ε⁻³` are produced by the same iteration bound
`K ≍ 4LΔ₀/ε²` multiplied by two different unit prices; nothing else differs.  See
`Optrates.Cost` for why those two prices are one formula at two exponents.

**Not formalized here** (L3+, per the plan's layering): SGD's `ε⁻⁴` *under an unbiased
stochastic oracle over an adaptive filtration*, SPIDER's `ε⁻³`, and Q-SPIDER's `ε⁻⁵ᐟ²`.
The `ε⁻⁴` below is the deterministic-surrogate version — a minibatch large enough to give
a *deterministic* accuracy guarantee — which is a strictly stronger oracle assumption than
SGD's and therefore not a reproduction of Ghadimi–Lan.  Stating this distinction rather
than eliding it is the point of the layering.
-/

section
open ShiOptRates

open Finset MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {L : ℝ}

/-- The accuracy `ε/√2` squares to exactly half the error budget, which is the hypothesis
`exists_grad_le_of_const_schedule` asks for. -/
theorem sq_eps_div_sqrt_two (ε : ℝ) : (ε / Real.sqrt 2) ^ 2 = ε ^ 2 / 2 := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

theorem solution (hL : 0 < L) (hQ : QuadUpper f g L) {fstar ε : ℝ} (hε : 0 < ε)
    (x : ℕ → E) (gd : ℕ → E) (K : ℕ) (hK : 0 < K) (hlow : fstar ≤ f (x K))
    (hstep : ∀ k < K, x (k + 1) = x k - L⁻¹ • gd k)
    (herr : ∀ k < K, ‖gd k - g (x k)‖ ≤ ε / Real.sqrt 2)
    (hKbig : 4 * L * (f (x 0) - fstar) / ε ^ 2 ≤ (K : ℝ)) :
    ∃ k < K, ‖g (x k)‖ ≤ ε :=
  exists_grad_le_of_const_schedule hL hQ hε x gd (fun _ => ε / Real.sqrt 2) K hK hlow
    hstep herr (fun _ _ => le_of_eq (sq_eps_div_sqrt_two ε)) hKbig

end
