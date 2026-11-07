-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobi_theta_factor_mul_logDerivative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:51:00.019316+00:00
-- url     : https://prove2.me/submissions/9ad735ba-bd4d-4097-acb4-20206b272a2b

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiGeometricSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_one_sub_X_pow_mul_jacobiMinusLogDerivative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_one_add_X_pow_mul_jacobiPlusLogDerivative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiEulerSixProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiEulerSquareProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiTriangularProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalIntegerThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiEulerSixProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiEulerSquareProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiThetaProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiTriangularProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalIntegerThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiGeometricSeries

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (n : ℕ) :
    (((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
        (1 + PowerSeries.X ^ (2 * n + 1)) ^ 2) *
      jacobiThetaLogDerivativeSummand n =
    PowerSeries.derivative ℚ
      (((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
        (1 + PowerSeries.X ^ (2 * n + 1)) ^ 2) := by
  have he := one_sub_X_pow_mul_jacobiMinusLogDerivative
    (show 2 * (n + 1) ≠ 0 by omega)
  have ho := one_add_X_pow_mul_jacobiPlusLogDerivative
    (show 2 * n + 1 ≠ 0 by omega)
  rw [(PowerSeries.derivative ℚ).leibniz,
    PowerSeries.derivative_pow]
  simp only [smul_eq_mul, jacobiThetaLogDerivativeSummand]
  rw [← he, ← ho]
  ring
end QEC.Coding.TannerLiftedProduct
