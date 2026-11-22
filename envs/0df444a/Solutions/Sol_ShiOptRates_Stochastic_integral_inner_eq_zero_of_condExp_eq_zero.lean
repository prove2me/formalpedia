-- Prove2me | solution 1 for ShiOptRates.Stochastic.integral_inner_eq_zero_of_condExp_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-08T22:52:59.001548+00:00
-- url     : https://prove2.me/submissions/409dcbb0-7041-4262-80ad-5b0e76c20524

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/Stochastic/Bridge.lean
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
import Theorems.Thm_ShiOptRates_Stochastic_integral_inner_condExp
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
# L3d — From a martingale difference to `L²` orthogonality

`Optrates.Stochastic.Accumulation` proves the `√K` accumulation law from an `L²`
orthogonality hypothesis, `∫ ⟪eₖ, ξₖ⟫ = 0`.  This file discharges that hypothesis from the
condition an actual stochastic algorithm satisfies: `ξₖ` is a martingale difference with
respect to a filtration to which `eₖ` is adapted.

This is the filtration layer the plan flagged as the likely sink.  It turns out to be
short, because Mathlib's `condExp_bilin_of_aestronglyMeasurable_left` already provides the
pull-out property for a general continuous bilinear map — so the vector-valued case needs
no more work than the scalar one, once the real inner product is packaged as such a map.

## Main definitions

* `innerBilin` — the real inner product as a continuous bilinear map, the form Mathlib's
  pull-out lemma consumes.

## Main results

* `integral_inner_eq_zero_of_condExp_eq_zero` — the tower-property step:
  `E[ξ | m] = 0` and `e` `m`-measurable give `E⟪e, ξ⟫ = 0`.
* `accumulation_sq_of_martingale` — **`√K` accumulation under a genuine filtration**:
  adapted error, martingale-difference increments, bounded conditional second moments.
-/

section
open ShiOptRates
open ShiOptRates.Stochastic

open MeasureTheory Filter
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem solution (hm : m ≤ mΩ)
    [SigmaFinite (μ.trim hm)] {e ξ : Ω → E}
    (he : AEStronglyMeasurable[m] e μ) (hξ : Integrable ξ μ)
    (hprod : Integrable (fun ω => ⟪e ω, ξ ω⟫_ℝ) μ)
    (hmart : μ[ξ | m] =ᵐ[μ] 0) :
    ∫ ω, ⟪e ω, ξ ω⟫_ℝ ∂μ = 0 := by
  rw [integral_inner_condExp hm he hξ hprod hmart]
  simp

end
