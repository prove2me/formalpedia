-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalE4Ratio_reciprocal_field_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:36:44.559145+00:00
-- url     : https://prove2.me/submissions/f256a60d-8ec6-4556-bdc3-bb16fc08d1ed

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicFractionRoot
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationChartEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalE4Equation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalReciprocalE4NormalizedEquation_coeff_degree
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphicJFraction_coefficient
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4Ratio_original_field_root
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ReciprocalPolynomialCoefficients_reflectCoefficients_root_field
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
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
local notation "R" => LPSOriginalHolomorphicRing
local notation "H" => LPSOriginalHolomorphicFractionField
local notation "P" => Polynomial ℂ
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k) :
    (lpsOriginalReciprocalE4MonicEquation N k A).eval₂
      (Polynomial.eval₂RingHom ((algebraMap R H).comp (algebraMap ℂ R))
        (algebraMap R H lpsOriginalJHolomorphic)⁻¹)
      ((algebraMap R H (lpsOriginalLevelFormHolomorphic N k A)) /
        (algebraMap R H (lpsOriginalE4PowerHolomorphic k))) = 0 := by
  let j := algebraMap R H lpsOriginalJHolomorphic
  have hj : j ≠ 0 := by
    intro hz
    have he : lpsOriginalJHolomorphic = 0 :=
      (IsFractionRing.injective R H) (hz.trans (map_zero _).symm)
    have hx : lpsOriginalJHolomorphicEval Polynomial.X = 0 := by
      simpa only [lpsOriginalJHolomorphicEval, Polynomial.aeval_X] using he
    exact Polynomial.X_ne_zero ((lpsOriginalJHolomorphicEval_injective)
      (hx.trans (map_zero _).symm))
  apply QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients.reflectCoefficients_root_field
    ((algebraMap R H).comp (algebraMap ℂ R))
    (k * Nat.card (LPSOriginalMeromorphicCosets N))
    (lpsOriginalReciprocalE4NormalizedEquation N k A)
    (lpsOriginalReciprocalE4NormalizedEquation_coeff_degree N k A)
    j _ hj
  rw [lpsOriginalReciprocalE4NormalizedEquation, Polynomial.eval₂_mul]
  have hr := lpsOriginalE4Ratio_original_field_root N k A
  rw [lpsOriginalHolomorphicJFraction_coefficient] at hr
  rw [hr, mul_zero]
end QEC.Coding.TannerLiftedProduct
