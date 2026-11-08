-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalE4MonicEquation_monic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:42:45.394208+00:00
-- url     : https://prove2.me/submissions/b708823d-2523-44e4-adeb-5872f3718020

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicFractionRoot
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationChartEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalE4Equation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4DenominatorEquation_coeff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ReciprocalPolynomialCoefficients_reflectCoefficients_monic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicRatioEquation_degree
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
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k) :
    (lpsOriginalReciprocalE4MonicEquation N k A).Monic := by
  apply QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients.reflectCoefficients_monic
    (k * Nat.card (LPSOriginalMeromorphicCosets N))
    (Nat.card (LPSOriginalMeromorphicCosets N))
  · unfold lpsOriginalReciprocalE4NormalizedEquation
    apply Polynomial.natDegree_mul_le.trans
    simpa only [Polynomial.natDegree_C, zero_add] using
      lpsOriginalMeromorphicRatioEquation_degree N k A
        (lpsOriginalMeromorphicE4PowerAtLevel N k)
  · rw [lpsOriginalReciprocalE4NormalizedEquation, Polynomial.coeff_C_mul,
      lpsOriginalE4DenominatorEquation_coeff, ← mul_assoc,
      ← Polynomial.C_mul, inv_mul_cancel₀, Polynomial.C_1, one_mul]
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
end QEC.Coding.TannerLiftedProduct
