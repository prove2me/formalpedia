-- Prove2me | solution 1 for ShiOptRates.Stochastic.accumulation_sq_stopped
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-08T23:00:12.890957+00:00
-- url     : https://prove2.me/submissions/285ab3cb-f18b-45cc-abcd-4a21fcfc49a9

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/Stochastic/Stopped.lean
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
import Definitions.Def_ShiOptrates_Stochastic_Stopped
import Theorems.Thm_ShiOptRates_Stochastic_accumulation_sq
import Theorems.Thm_ShiOptRates_Stochastic_integral_inner_eq_zero_of_condExp_eq_zero
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
# The accumulation law at a stopped time

`accumulation_sq` bounds `E‖e_K‖²` at a *fixed* index `K`.  Algorithms that stop
adaptively — SPIDER returns as soon as `‖vₜ‖ ≤ 2ε` — need the bound at the **random** index
`τ`, and the naive route fails: conditioning on `{τ = k}` destroys the unconditional
variance bound, which is exactly why `Spider.output_critical` is stated pathwise and why
Sidford–Zhang import Fang et al.'s Theorem 1 rather than reproving it.

The fix is to stop the process rather than the bound.  Write

`s_k = e_{τ ∧ k}`,  so that  `s_{k+1} = s_k + 1_{k < τ} ξ_k`,

and observe that `1_{k < τ} s_k` is still `ℱ_k`-measurable, so the *same* pull-out
(`integral_inner_condExp`) gives orthogonality of the stopped increments.  Then
`accumulation_sq` applies verbatim and the constant does not change:

`E‖e_{τ∧K}‖² ≤ E‖e_0‖² + K δ².`

## Main results

* `stopped_orthogonal` — the stopped increments inherit `L²` orthogonality.
* `accumulation_sq_stopped` — the accumulation law at a stopped time, same constant.
* `stopped_eq_of_le` — `s K = e_τ` when `τ ≤ K`, so the bound is about `e_τ` itself.
* `prob_stopped_error_large_le` — Markov: the accuracy event
  `‖e_τ‖ ≤ ε` fails with probability at most `(E‖e_0‖² + K δ²)/ε²`.  This is what feeds
  `Spider.output_critical`'s hypothesis.
-/

section
open ShiOptRates
open ShiOptRates.Stochastic

open MeasureTheory Filter
open scoped InnerProductSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Moving the stopping indicator from the increment to the accumulated error. -/
theorem inner_stopped (s ξ : ℕ → Ω → E) (τ : Ω → ℕ) (k : ℕ) (ω : Ω) :
    ⟪s k ω, stoppedIncr ξ τ k ω⟫_ℝ = ⟪stoppedFactor s τ k ω, ξ k ω⟫_ℝ := by
  by_cases h : k < τ ω <;> simp [stoppedIncr, stoppedFactor, h]

/-- **The stopped increments are still orthogonal to the past.**  The indicator `1_{k < τ}`
is `ℱ_k`-measurable, so it rides along inside the conditional expectation and the
martingale-difference property is untouched. -/
theorem stopped_orthogonal [IsFiniteMeasure μ] {ℱ : Filtration ℕ mΩ}
    (s ξ : ℕ → Ω → E) (τ : Ω → ℕ) (k : ℕ)
    (hfac : AEStronglyMeasurable[ℱ k] (stoppedFactor s τ k) μ)
    (hxint : Integrable (ξ k) μ)
    (hprod : Integrable (fun ω => ⟪stoppedFactor s τ k ω, ξ k ω⟫_ℝ) μ)
    (hmart : μ[ξ k | ℱ k] =ᵐ[μ] 0) :
    ∫ ω, ⟪s k ω, stoppedIncr ξ τ k ω⟫_ℝ ∂μ = 0 := by
  rw [integral_congr_ae (Filter.Eventually.of_forall (inner_stopped s ξ τ k))]
  exact integral_inner_eq_zero_of_condExp_eq_zero (ℱ.le k) hfac hxint hprod hmart

theorem solution [IsFiniteMeasure μ] {ℱ : Filtration ℕ mΩ}
    {s ξ : ℕ → Ω → E} {τ : Ω → ℕ} {δ : ℝ} (K : ℕ)
    (hsrec : ∀ k ω, s (k + 1) ω = s k ω + stoppedIncr ξ τ k ω)
    (hsin : ∀ k, Integrable (fun ω => ‖s k ω‖ ^ 2) μ)
    (hxin : ∀ k, Integrable (fun ω => ‖ξ k ω‖ ^ 2) μ)
    (hzin : ∀ k, Integrable (fun ω => ‖stoppedIncr ξ τ k ω‖ ^ 2) μ)
    (hcin : ∀ k, Integrable (fun ω => ⟪s k ω, stoppedIncr ξ τ k ω⟫_ℝ) μ)
    (hfac : ∀ k, AEStronglyMeasurable[ℱ k] (stoppedFactor s τ k) μ)
    (hxint : ∀ k, Integrable (ξ k) μ)
    (hprod : ∀ k, Integrable (fun ω => ⟪stoppedFactor s τ k ω, ξ k ω⟫_ℝ) μ)
    (hmart : ∀ k, μ[ξ k | ℱ k] =ᵐ[μ] 0)
    (hbnd : ∀ k, ∫ ω, ‖ξ k ω‖ ^ 2 ∂μ ≤ δ ^ 2) :
    ∫ ω, ‖s K ω‖ ^ 2 ∂μ ≤ (∫ ω, ‖s 0 ω‖ ^ 2 ∂μ) + K * δ ^ 2 := by
  refine accumulation_sq K hsrec hsin hzin hcin
    (fun k => stopped_orthogonal s ξ τ k (hfac k) (hxint k) (hprod k) (hmart k)) ?_
  -- stopping only shrinks the increments
  intro k
  have hpt : ∀ ω, ‖stoppedIncr ξ τ k ω‖ ^ 2 ≤ ‖ξ k ω‖ ^ 2 := by
    intro ω
    by_cases h : k < τ ω
    · simp [stoppedIncr, h]
    · have hz : stoppedIncr ξ τ k ω = 0 := by simp [stoppedIncr, h]
      rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
      positivity
  exact le_trans (integral_mono (hzin k) (hxin k) hpt) (hbnd k)

end
