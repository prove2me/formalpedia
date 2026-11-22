-- Prove2me | solution 1 for ShiOptRates.Stochastic.sgd_expectedDescent
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-08T22:53:41.056536+00:00
-- url     : https://prove2.me/submissions/5d1ae5cf-bde9-4662-8d2f-a9180de2f876

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
import Theorems.Thm_ShiOptRates_Stochastic_integral_inner_condExp
import Theorems.Thm_ShiOptRates_Stochastic_integral_le_of_condExp_le
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

theorem solution (hQ : QuadUpper f g L) (hL : 0 < L)
    (hs : 0 < hstep) (hsL : hstep ≤ 1 / L)
    (ℱ : Filtration ℕ mΩ) (x gd : ℕ → Ω → E) (K : ℕ)
    (hxstep : ∀ k, k < K → ∀ ω, x (k + 1) ω = x k ω - hstep • gd k ω)
    (hadapt : ∀ k, k < K → AEStronglyMeasurable[ℱ k] (fun ω => g (x k ω)) μ)
    (hgint : ∀ k, k < K → Integrable (gd k) μ)
    (hg2 : ∀ k, k < K → Integrable (fun ω => ‖gd k ω‖ ^ 2) μ)
    (hfint : ∀ k, k ≤ K → Integrable (fun ω => f (x k ω)) μ)
    (hgradint : ∀ k, k < K → Integrable (fun ω => ‖g (x k ω)‖ ^ 2) μ)
    (hcross : ∀ k, k < K → Integrable (fun ω => ⟪g (x k ω), gd k ω⟫_ℝ) μ)
    (hunb : ∀ k, k < K → μ[gd k | ℱ k] =ᵐ[μ] fun ω => g (x k ω))
    (hsm : ∀ k, k < K →
      μ[fun ω => ‖gd k ω‖ ^ 2 | ℱ k] ≤ᵐ[μ] fun ω => ‖g (x k ω)‖ ^ 2 + σ ^ 2) :
    ExpectedDescent (fun k => ∫ ω, f (x k ω) ∂μ)
      (fun k => ∫ ω, ‖g (x k ω)‖ ^ 2 ∂μ) hstep L σ K := by
  intro k hk
  simp only
  -- (1) the pathwise descent inequality along the step
  have hpath : ∀ ω, f (x (k + 1) ω)
      ≤ f (x k ω) - hstep * ⟪g (x k ω), gd k ω⟫_ℝ
        + L * hstep ^ 2 / 2 * ‖gd k ω‖ ^ 2 := by
    intro ω
    have hd := hQ (x k ω) (x k ω - hstep • gd k ω)
    have hyx : x k ω - hstep • gd k ω - x k ω = -(hstep • gd k ω) := by abel
    rw [hyx, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs] at hd
    rw [hxstep k hk ω]
    calc f (x k ω - hstep • gd k ω)
        ≤ f (x k ω) + -(hstep * ⟪g (x k ω), gd k ω⟫_ℝ)
            + L / 2 * (hstep ^ 2 * ‖gd k ω‖ ^ 2) := hd
      _ = f (x k ω) - hstep * ⟪g (x k ω), gd k ω⟫_ℝ
            + L * hstep ^ 2 / 2 * ‖gd k ω‖ ^ 2 := by ring
  -- (2) integrate it
  have hc : Integrable (fun ω => hstep * ⟪g (x k ω), gd k ω⟫_ℝ) μ := (hcross k hk).const_mul _
  have h1 : Integrable (fun ω => f (x k ω) - hstep * ⟪g (x k ω), gd k ω⟫_ℝ) μ :=
    (hfint k hk.le).sub hc
  have h2 : Integrable (fun ω => L * hstep ^ 2 / 2 * ‖gd k ω‖ ^ 2) μ := (hg2 k hk).const_mul _
  have hmono : ∫ ω, f (x (k + 1) ω) ∂μ
      ≤ ∫ ω, (f (x k ω) - hstep * ⟪g (x k ω), gd k ω⟫_ℝ
          + L * hstep ^ 2 / 2 * ‖gd k ω‖ ^ 2) ∂μ :=
    integral_mono (hfint (k + 1) hk) (h1.add h2) hpath
  -- (3) the tower property turns the cross term into `E‖∇f(xₖ)‖²`
  have htower : ∫ ω, ⟪g (x k ω), gd k ω⟫_ℝ ∂μ = ∫ ω, ‖g (x k ω)‖ ^ 2 ∂μ := by
    rw [integral_inner_condExp (ℱ.le k) (hadapt k hk) (hgint k hk) (hcross k hk) (hunb k hk)]
    exact integral_congr_ae (Filter.Eventually.of_forall
      fun ω => real_inner_self_eq_norm_sq (g (x k ω)))
  -- (4) the conditional second-moment bound integrates
  have huniv : μ.real (Set.univ : Set Ω) = 1 := by simp [Measure.real]
  have hsecond : ∫ ω, ‖gd k ω‖ ^ 2 ∂μ ≤ (∫ ω, ‖g (x k ω)‖ ^ 2 ∂μ) + σ ^ 2 := by
    have hv : Integrable (fun ω => ‖g (x k ω)‖ ^ 2 + σ ^ 2) μ :=
      (hgradint k hk).add (integrable_const _)
    have hh := integral_le_of_condExp_le (ℱ.le k) (hg2 k hk) hv (hsm k hk)
    rwa [integral_add (hgradint k hk) (integrable_const _), integral_const, huniv,
      one_smul] at hh
  -- (5) assemble
  have hsplit : ∫ ω, (f (x k ω) - hstep * ⟪g (x k ω), gd k ω⟫_ℝ
      + L * hstep ^ 2 / 2 * ‖gd k ω‖ ^ 2) ∂μ
      = (∫ ω, f (x k ω) ∂μ) - hstep * (∫ ω, ‖g (x k ω)‖ ^ 2 ∂μ)
        + L * hstep ^ 2 / 2 * ∫ ω, ‖gd k ω‖ ^ 2 ∂μ := by
    rw [integral_add h1 h2, integral_sub (hfint k hk.le) hc, integral_const_mul,
      integral_const_mul, htower]
  rw [hsplit] at hmono
  have hbnn : 0 ≤ ∫ ω, ‖g (x k ω)‖ ^ 2 ∂μ := integral_nonneg fun ω => by positivity
  have hcoef : 0 ≤ L * hstep ^ 2 / 2 := by positivity
  have hLh : L * hstep ≤ 1 := by rw [le_div_iff₀ hL] at hsL; linarith
  have hsec' : L * hstep ^ 2 / 2 * ∫ ω, ‖gd k ω‖ ^ 2 ∂μ
      ≤ L * hstep ^ 2 / 2 * ((∫ ω, ‖g (x k ω)‖ ^ 2 ∂μ) + σ ^ 2) :=
    mul_le_mul_of_nonneg_left hsecond hcoef
  have hcc : L * hstep * hstep ≤ 1 * hstep := mul_le_mul_of_nonneg_right hLh hs.le
  have hc2 : L * hstep ^ 2 ≤ hstep := by nlinarith [hcc]
  have hprod : 0 ≤ (hstep - L * hstep ^ 2) * ∫ ω, ‖g (x k ω)‖ ^ 2 ∂μ :=
    mul_nonneg (by linarith) hbnn
  linarith [hmono, hsec', hprod]

end
