-- Prove2me | solution 1 for TestFunctionGradientIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:09:39.162912+00:00
-- url     : https://prove2.me/submissions/3834ad86-e483-4830-ab6d-2ef3409a4a4b

import Definitions.Def_PHigherOrder_Plane
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.L2Space
import Definitions.Def_PHigherOrder_TestFunctionGradientIntegral

set_option autoImplicit false

theorem _root_.solution (φ : Plane → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hsupp : HasCompactSupport φ) :
    ∫ x : Plane, gradient φ x = 0 := by
  have hdφ : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hfd : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  have hfdcs : HasCompactSupport (fderiv ℝ φ) := hsupp.fderiv ℝ
  -- The directional identity, in every direction, by integration by parts against the
  -- constant function `1`:  its derivative vanishes, so the boundary-free parts formula
  -- `∫ f · D_v g = - ∫ D_v f · g` collapses to `∫ D_v φ = 0`.  The asymmetry of the
  -- differentiability hypotheses is what makes this legitimate:  `f` is only required to be
  -- differentiable on `tsupport g`, and `g = φ` is differentiable everywhere.
  have hdir : ∀ v : Plane, ∫ x : Plane, fderiv ℝ φ x v = 0 := by
    intro v
    have hint : MeasureTheory.Integrable (fun x : Plane => fderiv ℝ φ x v) :=
      (hfd.clm_apply continuous_const).integrable_of_hasCompactSupport
        (hfdcs.comp_left (g := fun L : Plane →L[ℝ] ℝ => L v) (by simp))
    have hintφ : MeasureTheory.Integrable φ :=
      hφ.continuous.integrable_of_hasCompactSupport hsupp
    have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (MeasureTheory.volume : MeasureTheory.Measure Plane))
      (f := fun _ : Plane => (1 : ℝ)) (g := φ) (v := v)
      (by simp)
      (by simpa using hint)
      (by simpa using hintφ)
      (fun x _ => differentiableAt_const _)
      (fun x _ => hdφ x)
    simpa using key
  -- The gradient field is continuous with compact support, hence integrable, so the vector
  -- identity follows from the vanishing of all of its inner products.
  have hgint : MeasureTheory.Integrable (fun x : Plane => gradient φ x) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((InnerProductSpace.toDual ℝ Plane).symm.continuous).comp hfd
    · exact hfdcs.comp_left
        (g := fun L : Plane →L[ℝ] ℝ => (InnerProductSpace.toDual ℝ Plane).symm L) (by simp)
  refine integral_eq_zero_of_forall_integral_inner_eq_zero ℝ _ hgint ?_
  intro c
  simpa [inner_gradient_right] using hdir c
