-- Prove2me | solution 1 for Zeta23.mu_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:05:43.177349+00:00
-- url     : https://prove2.me/submissions/6c87129b-becf-45cd-a0d4-f4332a5e06db

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs

-- from Zeta23.GammaFacts
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/GammaFacts.lean — the even and smooth clauses of H-Γ [eq:mufacts].

Paper [eq:mufacts] asserts: "μ is even, smooth, increasing in |τ|, μ ≥ μ(0) > −1,
μ(τ) = (1/2π)log(|τ|/2π) + O(τ⁻²), μ′(τ) ≪ |τ|⁻¹ (|τ| ≥ 1)" plus [eq:muints].

This file proves the EVEN and SMOOTH clauses against Mathlib's
Complex.digamma (= logDeriv Gamma):
  • digamma_conj : Γ'/Γ commutes with conjugation (from Complex.Gamma_conj +
    deriv_conj_conj);
  • mu_even : μ(−τ) = μ(τ);
  • mu_smooth : ContDiff ℝ ∞ μ (Γ is holomorphic hence analytic on Re > 0,
    so digamma is analytic there; compose with the affine line τ ↦ 1/4 + iτ/2).

The remaining clauses (monotonicity in |τ|, μ(0) > −1, the Stirling asymptotic
with O(τ⁻²), the derivative bound, and [eq:muints]) are the fields of
Zeta23.GammaFacts in Hypotheses.lean; they are proved in the files under
Zeta23/GammaFacts/ and assembled in Zeta23/GammaFacts/Complete.lean (`gammaFacts`).
The route: the digamma partial-fraction series
  digamma z = −γ_E + Σ_{n≥0} (1/(n+1) − 1/(n+z))  on ℂ ∖ (−ℕ)
(Zeta23/GammaFacts/Series.lean), from which monotonicity and μ ≥ μ(0) are termwise
monotonicity of (n+σ)/((n+σ)²+t²) in t², μ(0) > −1 is a finite partial-sum bound,
and the derivative bound is termwise differentiation; the Stirling clause uses a
vertical-line Stirling estimate (Zeta23/GammaFacts/StirlingVert.lean,
Zeta23/Analytic/Stirling.lean), and the integrals [eq:muints] follow by integrating
the asymptotic (Zeta23/GammaFacts/IntMu.lean).
-/

namespace Zeta23

open Complex

open scoped ContDiff



/-- The open right half-plane where Γ is holomorphic and nonvanishing. -/
lemma gamma_ne_neg_nat {z : ℂ} (hz : 0 < z.re) : ∀ m : ℕ, z ≠ -m := by
  intro m h
  rw [h] at hz
  simp only [Complex.neg_re, Complex.natCast_re] at hz
  exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg m))) hz

lemma analyticAt_digamma {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ Complex.digamma z := by
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hGamD : DifferentiableOn ℂ Complex.Gamma {w : ℂ | 0 < w.re} := fun w hw =>
    (Complex.differentiableAt_Gamma w (gamma_ne_neg_nat hw)).differentiableWithinAt
  have hGamA := hGamD.analyticOnNhd hU
  have h1 : AnalyticAt ℂ (deriv Complex.Gamma) z := (hGamA z hz).deriv
  have h2 : AnalyticAt ℂ Complex.Gamma z := hGamA z hz
  have h3 : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero (gamma_ne_neg_nat hz)
  have h4 := h1.div h2 h3
  exact h4.congr (by
    filter_upwards with w
    rw [Complex.digamma_def, logDeriv_apply]
    rfl)

-- The set_option below is Mathlib's own workaround for instance-path defeq on
-- IsScalarTower ℝ ℂ ℂ (cf. Analysis/CStarAlgebra/ContinuousFunctionalCalculus/
-- RealImaginaryPart.lean, "fails to find IsScalarTower ℝ ℂ A").

end Zeta23
open Zeta23
open Complex
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem solution : ContDiff ℝ ∞ mu := by
  have hc : ContDiff ℝ ∞ (fun τ : ℝ => (1 / 4 + Complex.I * (τ : ℂ) / 2 : ℂ)) := by
    have h1 : ContDiff ℝ ∞ (fun τ : ℝ => (τ : ℂ)) := Complex.ofRealCLM.contDiff
    have h2 : ContDiff ℝ ∞ (fun τ : ℝ => Complex.I * (τ : ℂ)) := contDiff_const.mul h1
    have h3 : ContDiff ℝ ∞ (fun τ : ℝ => Complex.I * (τ : ℂ) / 2) := by
      simpa [div_eq_mul_inv] using h2.mul contDiff_const
    exact contDiff_const.add h3
  refine contDiff_iff_contDiffAt.mpr fun τ => ?_
  have hz : (0 : ℝ) < (1 / 4 + Complex.I * (τ : ℂ) / 2 : ℂ).re := by
    simp
  have h4' : AnalyticAt ℝ Complex.digamma (1 / 4 + Complex.I * (τ : ℂ) / 2) :=
    AnalyticAt.restrictScalars (analyticAt_digamma hz)
  have h4 : ContDiffAt ℝ ∞ Complex.digamma (1 / 4 + Complex.I * (τ : ℂ) / 2) :=
    h4'.contDiffAt
  have h5 : ContDiffAt ℝ ∞
      (fun τ : ℝ => Complex.digamma (1 / 4 + Complex.I * (τ : ℂ) / 2)) τ :=
    h4.comp τ hc.contDiffAt
  have h6 : ContDiffAt ℝ ∞
      (fun τ : ℝ => (Complex.digamma (1 / 4 + Complex.I * (τ : ℂ) / 2)).re) τ :=
    (Complex.reCLM.contDiff.contDiffAt).comp τ h5
  have h7 : ContDiffAt ℝ ∞ mu τ := by
    have := (contDiffAt_const (c := (1 / (2 * Real.pi) : ℝ))).mul h6
    exact (this.sub contDiffAt_const)
  exact h7
