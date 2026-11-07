-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.integral_of_prime_multiple_and_localizedIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:34:42.256382+00:00
-- url     : https://prove2.me/submissions/cd27430e-7bac-499e-805b-6df3d13177a0

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Algebra.Prime.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFiberDescent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primePower_dvd_of_localized_dvd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (P : Ideal R) [P.IsPrime] (J K : Type*) [Field J] [Field K]
    [Algebra R J] [IsFractionRing R J]
    [Algebra (Localization.AtPrime P) J]
    [IsScalarTower R (Localization.AtPrime P) J]
    [IsFractionRing (Localization.AtPrime P) J]
    [Algebra R K] [Algebra (Localization.AtPrime P) K] [Algebra J K]
    [IsScalarTower R J K] [IsScalarTower (Localization.AtPrime P) J K]
    [IsScalarTower R (Localization.AtPrime P) K]
    [FaithfulSMul R K] [FaithfulSMul (Localization.AtPrime P) K]
    [IsIntegrallyClosed (Localization.AtPrime P)]
    (a : R) (hP : P = Ideal.span {a}) (ha : Prime a) (y : K)
    (hR : IsIntegral R (algebraMap R K a*y))
    (hG : IsIntegral (Localization.AtPrime P) y) : IsIntegral R y := by
  let G := Localization.AtPrime P
  let x := algebraMap R K a*y
  have hxG : IsIntegral G x := hR.tower_top
  have hRG : (minpoly R x).map (algebraMap R G) = minpoly G x := by
    apply Polynomial.map_injective (algebraMap G J) (IsFractionRing.injective G J)
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq R G J,
      ← minpoly.isIntegrallyClosed_eq_field_fractions' J hR,
      ← minpoly.isIntegrallyClosed_eq_field_fractions' J hxG]
  have haG : algebraMap R G a ≠ 0 := by
    intro h
    apply ha.ne_zero
    exact (FaithfulSMul.algebraMap_injective R G) (h.trans (map_zero _).symm)
  have hscale : minpoly G x = (minpoly G y).scaleRoots (algebraMap R G a) := by
    have h := IsIntegrallyClosed.minpoly_smul (R := G) haG hG
    simpa only [Algebra.smul_def, ← IsScalarTower.algebraMap_apply R G K] using h
  have hlifts : minpoly G y ∈ Polynomial.lifts (algebraMap R G) := by
    apply (Polynomial.lifts_iff_coeff_lifts _).mpr
    intro i
    let n := (minpoly G y).natDegree-i
    have hc : algebraMap R G ((minpoly R x).coeff i) =
        (algebraMap R G a)^n * (minpoly G y).coeff i := by
      have h := congrArg (fun f : Polynomial G => f.coeff i) (hRG.trans hscale)
      rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots] at h
      exact h.trans (mul_comm _ _)
    have hd : a^n ∣ (minpoly R x).coeff i :=
      primePower_dvd_of_localized_dvd P a hP ha n _ ⟨_,hc⟩
    obtain ⟨b,hb⟩ := hd
    refine ⟨b,?_⟩
    apply mul_left_cancel₀ (pow_ne_zero n haG)
    calc
      (algebraMap R G a)^n * algebraMap R G b =
          algebraMap R G ((minpoly R x).coeff i) := by rw [hb,map_mul,map_pow]
      _ = (algebraMap R G a)^n * (minpoly G y).coeff i := hc
  obtain ⟨Q,hQ,-,hmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts (minpoly.monic hG)
  refine ⟨Q,hmon,?_⟩
  have h := minpoly.aeval G y
  rw [← hQ,Polynomial.aeval_map_algebraMap] at h
  exact h
end QEC.Coding.AlgebraicGeometry
