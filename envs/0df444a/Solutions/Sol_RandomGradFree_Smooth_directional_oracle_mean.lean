-- Prove2me | solution 1 for RandomGradFree.Smooth.directional_oracle_mean
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:27:27.761193+00:00
-- url     : https://prove2.me/submissions/aa647048-f2f2-4428-891b-c725f0dc4807

import Mathlib

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Smooth

open scoped RealInnerProductSpace in
theorem aux_dom_cov_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (g y : E) :
    ⟪covarianceOperator (stdGaussian E) g, y⟫ = ⟪g, y⟫ := by
  have hμ : MemLp id 2 (stdGaussian E) := IsGaussian.memLp_two_id
  rw [covarianceOperator_inner hμ]
  have h := covarianceBilin_apply hμ g y
  rw [covarianceBilin_stdGaussian] at h
  have h0 : ∫ z, id z ∂(stdGaussian E) = 0 := integral_id_stdGaussian
  simp only [h0, sub_zero] at h
  rw [← h]
  exact innerSL_apply_apply ℝ g y

end RandomGradFree.Smooth

open RandomGradFree.Smooth
open MeasureTheory ProbabilityTheory

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (x : E) (hfx : DifferentiableAt ℝ f x) :
    ∫ u, fderiv ℝ f x u • u ∂(stdGaussian E) = gradient f x := by
  have hμ : MemLp id 2 (stdGaussian E) := IsGaussian.memLp_two_id
  have hL : ∀ u, fderiv ℝ f x u = inner ℝ (gradient f x) u := by
    intro u
    rw [gradient, InnerProductSpace.toDual_symm_apply]
  simp_rw [hL]
  rw [← covarianceOperator_apply hμ]
  refine ext_inner_right ℝ fun y => ?_
  exact aux_dom_cov_inner _ _
