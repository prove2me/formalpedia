-- Prove2me | solution 1 for Rudin.ch10_change_of_variables
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T20:29:59.189729+00:00
-- url     : https://prove2.me/submissions/ef23a959-6642-4ca9-9f62-d0ef6d77e813

import Mathlib
import Definitions.Def_Rudin_ch10_forms
set_option autoImplicit false
open Filter Topology MeasureTheory Rudin
theorem solution (k : ℕ) (E : Set (Fin k → ℝ)) (hE : IsOpen E)
    (T : (Fin k → ℝ) → (Fin k → ℝ)) (hT : ContDiffOn ℝ 1 T E) (hinj : Set.InjOn T E)
    (hJ : ∀ x ∈ E, jacobian T id x ≠ 0)
    (f : (Fin k → ℝ) → ℝ) (hf : Continuous f) (hsupp : HasCompactSupport f)
    (hsub : tsupport f ⊆ T '' E) :
    (∫ y, f y) = ∫ x in E, f (T x) * |jacobian T id x| := by
  classical
  have hdiff : ∀ x ∈ E, DifferentiableAt ℝ T x := fun x hx =>
    (hT.contDiffAt (hE.mem_nhds hx)).differentiableAt (by norm_num)
  have hjac : ∀ x ∈ E, jacobian T id x = (fderiv ℝ T x).det := by
    intro x hx
    change Matrix.det (Matrix.of fun i j : Fin k => partialDeriv (fun v => T v (id i)) j x) =
      LinearMap.det (fderiv ℝ T x).toLinearMap
    rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin k))]
    congr 1
    ext i j
    simp only [jacobian, partialDeriv, Matrix.of_apply, LinearMap.toMatrix_apply,
      Pi.basisFun_apply, Pi.basisFun_repr, id_eq]
    have hd := (hasFDerivAt_pi'.mp (hdiff x hx).hasFDerivAt) i
    rw [hd.fderiv]
    rfl
  calc
    (∫ y, f y) = ∫ y in T '' E, f y := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      by_contra hfy
      exact hy (hsub (subset_tsupport f hfy))
    _ = ∫ x in E, |(fderiv ℝ T x).det| • f (T x) :=
      integral_image_eq_integral_abs_det_fderiv_smul volume hE.measurableSet
        (fun x hx => (hdiff x hx).hasFDerivAt.hasFDerivWithinAt) hinj f
    _ = ∫ x in E, f (T x) * |jacobian T id x| := by
      apply setIntegral_congr_fun hE.measurableSet
      intro x hx
      change |(fderiv ℝ T x).det| * f (T x) = f (T x) * |jacobian T id x|
      rw [hjac x hx, mul_comm]
#print axioms solution
