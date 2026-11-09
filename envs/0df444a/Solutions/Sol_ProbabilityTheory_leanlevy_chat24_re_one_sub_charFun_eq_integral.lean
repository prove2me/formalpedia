-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat24_re_one_sub_charFun_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T13:32:44.420917+00:00
-- url     : https://prove2.me/submissions/9810426a-d5a0-4863-ba19-f5154865219c

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators

private lemma chat24_integrable_charFun_integrand {μ : Measure ℝ} [IsFiniteMeasure μ] (ξ : ℝ) :
    Integrable (fun x : ℝ => exp ((↑(ξ * x) : ℂ) * I)) μ :=
  Integrable.of_bound
    ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id')).mul_const I
      |>.cexp.aestronglyMeasurable)
    1 (ae_of_all _ fun _ => le_of_eq (Complex.norm_exp_ofReal_mul_I _))


theorem solution
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (ξ : ℝ) :
    (1 - charFun μ ξ).re = ∫ x, (1 - Real.cos (ξ * x)) ∂μ := by
  have hint := chat24_integrable_charFun_integrand (μ := μ) ξ
  -- Express 1 - charFun as a single integral of (1 - exp(iξx))
  have h1 : 1 - charFun μ ξ = ∫ x : ℝ, (1 - exp ((↑(ξ * x) : ℂ) * I)) ∂μ := by
    have hcf : charFun μ ξ = ∫ x : ℝ, exp ((↑(ξ * x) : ℂ) * I) ∂μ := by
      rw [charFun_apply_real]; congr 1; ext x; congr 1; push_cast; ring
    rw [hcf]
    have h_one : (1 : ℂ) = ∫ _ : ℝ, (1 : ℂ) ∂μ := by simp [integral_const]
    conv_lhs => rw [h_one]
    exact (integral_sub (integrable_const (1 : ℂ)) hint).symm
  -- Take Re and commute through integral
  rw [h1, show (∫ x : ℝ, (1 - exp ((↑(ξ * x) : ℂ) * I)) ∂μ).re =
    ∫ x : ℝ, (1 - exp ((↑(ξ * x) : ℂ) * I)).re ∂μ from
    (integral_re (Integrable.sub (integrable_const 1) hint)).symm]
  -- Simplify Re(1 - exp(iξx)) = 1 - cos(ξx)
  congr 1; ext x
  simp only [sub_re, one_re, Complex.exp_ofReal_mul_I_re]

