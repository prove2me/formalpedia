-- Prove2me | solution 1 for ShiOptRates.Stochastic.sgd_rate
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-08T23:06:18.80195+00:00
-- url     : https://prove2.me/submissions/3dd040d4-703f-4e46-80f5-f82346c0b0ed

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/Stochastic/SGD.lean
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
import Theorems.Thm_ShiOptRates_Stochastic_exists_le_sq_of_stepsize
import Theorems.Thm_ShiOptRates_Stochastic_sgd_expectedDescent
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
# L3 / GL3 — SGD over an adaptive filtration

The layer the plan flagged as the hardest: the stochastic gradient at step `k` depends on
`x k`, which depends on all previous noise, so the analysis lives over a filtration and the
oracle contract is conditional.

The chain assembled here is:

`pathwise descent lemma` → `integrate` → `tower property (Bridge)` → `ExpectedDescent
(Recursion)` → `ε⁻⁴`.

The only genuinely martingale-theoretic step is the tower property, and it is discharged
by `integral_inner_condExp`: the `F_k`-measurable factor `∇f(xₖ)` is replaced by its
conditional expectation inside the inner product, turning the cross term
`E⟪∇f(xₖ), gₖ⟫` into `E‖∇f(xₖ)‖²`.

## Main results

* `sgd_expectedDescent` — an SGD trajectory's `(E f(xₖ), E‖∇f(xₖ)‖²)` satisfies
  `ExpectedDescent`.
* `sgd_rate` — **GL3**: `K ≥ 8 L Δ₀ σ² / ε⁴` iterations at stepsize `ε²/(2Lσ²)` give an
  iterate with `E‖∇f(xₖ)‖² ≤ ε²`.  The Ghadimi–Lan `ε⁻⁴`, with the constant explicit.
-/

section
open ShiOptRates
open ShiOptRates.Stochastic

open MeasureTheory Filter Finset
open scoped InnerProductSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {g : E → E} {L σ hstep : ℝ}

theorem solution (hQ : QuadUpper f g L) (hL : 0 < L) {σ ε fstar : ℝ}
    (hσ : 0 < σ) (hε : 0 < ε) (hεσ : ε ^ 2 ≤ 2 * σ ^ 2)
    (ℱ : Filtration ℕ mΩ) (x gd : ℕ → Ω → E) (K : ℕ) (hK : 0 < K)
    (hxstep : ∀ k, k < K → ∀ ω, x (k + 1) ω = x k ω - (ε ^ 2 / (2 * L * σ ^ 2)) • gd k ω)
    (hadapt : ∀ k, k < K → AEStronglyMeasurable[ℱ k] (fun ω => g (x k ω)) μ)
    (hgint : ∀ k, k < K → Integrable (gd k) μ)
    (hg2 : ∀ k, k < K → Integrable (fun ω => ‖gd k ω‖ ^ 2) μ)
    (hfint : ∀ k, k ≤ K → Integrable (fun ω => f (x k ω)) μ)
    (hgradint : ∀ k, k < K → Integrable (fun ω => ‖g (x k ω)‖ ^ 2) μ)
    (hcross : ∀ k, k < K → Integrable (fun ω => ⟪g (x k ω), gd k ω⟫_ℝ) μ)
    (hunb : ∀ k, k < K → μ[gd k | ℱ k] =ᵐ[μ] fun ω => g (x k ω))
    (hsm : ∀ k, k < K →
      μ[fun ω => ‖gd k ω‖ ^ 2 | ℱ k] ≤ᵐ[μ] fun ω => ‖g (x k ω)‖ ^ 2 + σ ^ 2)
    (hlow : fstar ≤ ∫ ω, f (x K ω) ∂μ)
    (hKbig : 8 * L * ((∫ ω, f (x 0 ω) ∂μ) - fstar) * σ ^ 2 / ε ^ 4 ≤ (K : ℝ)) :
    ∃ k < K, ∫ ω, ‖g (x k ω)‖ ^ 2 ∂μ ≤ ε ^ 2 := by
  set h0 : ℝ := ε ^ 2 / (2 * L * σ ^ 2) with hh0
  have hspos : 0 < h0 := by rw [hh0]; positivity
  have hsL : h0 ≤ 1 / L := by
    rw [hh0, div_le_div_iff₀ (by positivity) hL]
    nlinarith [hεσ, hL.le, sq_nonneg σ]
  have hrec := sgd_expectedDescent hQ hL hspos hsL ℱ x gd K hxstep hadapt hgint hg2 hfint
    hgradint hcross hunb hsm
  exact exists_le_sq_of_stepsize hε hL hσ hK hrec hlow hKbig

end
