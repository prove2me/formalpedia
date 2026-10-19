-- Prove2me | solution 1 for SpherePacking.ForMathlib.Fourier.fourier_precompose_linear_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/f71a0709-f796-498f-9c56-c888c1c4a6af

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open SpherePacking SpherePacking.ForMathlib SpherePacking.ForMathlib.Fourier
open scoped FourierTransform
open MeasureTheory
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace SpherePacking.ForMathlib.Fourier
theorem _root_.solution (A : V ≃ₗ[ℝ] V) (f : V → ℂ) (w : V) :
    𝓕 (fun x ↦ f (A x)) w =
      (abs (LinearMap.det (A : V →ₗ[ℝ] V)))⁻¹ •
        𝓕 f (((A.symm : V ≃ₗ[ℝ] V).toLinearMap).adjoint w) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  let B : V →L[ℝ] V := A.toContinuousLinearEquiv.toContinuousLinearMap
  let g : V → ℂ := fun x =>
    Complex.exp
      ((↑(-2 * Real.pi * @inner ℝ V _ x
        (((A.symm : V ≃ₗ[ℝ] V).toLinearMap).adjoint w)) : ℂ) * Complex.I) • f x
  have hinner (x : V) :
      @inner ℝ V _ (A x)
        (((A.symm : V ≃ₗ[ℝ] V).toLinearMap).adjoint w) =
          @inner ℝ V _ x w := by
    rw [LinearMap.adjoint_inner_right]
    simp
  have hchange :
      (∫ x : V, g x) =
        |LinearMap.det (A : V →ₗ[ℝ] V)| • ∫ x : V, g (A x) := by
    have h := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      (volume : Measure V) (s := Set.univ) (f := fun x : V => A x)
      (f' := fun _ : V => B) MeasurableSet.univ
      (fun x _ => B.hasFDerivAt.hasFDerivWithinAt)
      (Set.injOn_of_injective A.injective) g
    have hdetB : B.det = LinearMap.det (A : V →ₗ[ℝ] V) := by
      rfl
    calc
      (∫ x : V, g x) =
          ∫ x : V, |LinearMap.det (A : V →ₗ[ℝ] V)| • g (A x) := by
        simpa [Set.image_univ, A.surjective.range_eq, hdetB] using h
      _ = |LinearMap.det (A : V →ₗ[ℝ] V)| • ∫ x : V, g (A x) :=
        integral_smul _ _
  have hdet : LinearMap.det (A : V →ₗ[ℝ] V) ≠ 0 := by
    intro hzero
    have hcomp := LinearMap.det_comp
      ((A.symm : V ≃ₗ[ℝ] V).toLinearMap) (A : V →ₗ[ℝ] V)
    simp [hzero] at hcomp
  change (∫ x : V,
    Complex.exp ((↑(-2 * Real.pi * @inner ℝ V _ x w) : ℂ) * Complex.I) •
      f (A x)) = |LinearMap.det (A : V →ₗ[ℝ] V)|⁻¹ • ∫ x : V, g x
  have hleft :
      (∫ x : V,
        Complex.exp ((↑(-2 * Real.pi * @inner ℝ V _ x w) : ℂ) * Complex.I) •
          f (A x)) = ∫ x : V, g (A x) := by
    congr 1
    funext x
    simp [g, hinner]
  rw [hleft]
  calc
    (∫ x : V, g (A x)) =
        |LinearMap.det (A : V →ₗ[ℝ] V)|⁻¹ •
          (|LinearMap.det (A : V →ₗ[ℝ] V)| • ∫ x : V, g (A x)) := by
      rw [← mul_smul, inv_mul_cancel₀ (abs_ne_zero.mpr hdet), one_smul]
    _ = |LinearMap.det (A : V →ₗ[ℝ] V)|⁻¹ • ∫ x : V, g x := by
      rw [hchange]
end SpherePacking.ForMathlib.Fourier
