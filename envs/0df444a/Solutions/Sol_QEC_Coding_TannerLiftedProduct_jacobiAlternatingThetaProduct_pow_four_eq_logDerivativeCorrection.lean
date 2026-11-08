-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobiAlternatingThetaProduct_pow_four_eq_logDerivativeCorrection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:06:46.931175+00:00
-- url     : https://prove2.me/submissions/7f791c21-81ae-4d11-a9da-61bb8d4852c3

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareIdentity
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_jacobiSignedCubeSeries_sq_eq_jacobiEulerSixProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTriangularProduct_jacobiTriangularProduct_eq_rationalTriangularThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_isUnit_jacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_isUnit_jacobiTriangularProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiAlternatingThetaProduct_pow_four_mul_theta_triangular
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiSignedCubeSeries_sq_eq_theta_wronskian
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiThetaProduct_eq_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobi_cube_correction_factorization


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    jacobiAlternatingThetaProduct ^ 4 =
      1 + PowerSeries.C 4 * PowerSeries.X *
        jacobiLogDerivativeDifference := by
  apply (isUnit_jacobiThetaProduct.mul
    isUnit_jacobiTriangularProduct).mul_right_cancel
  calc
    jacobiAlternatingThetaProduct ^ 4 *
        (jacobiThetaProduct * jacobiTriangularProduct) =
      jacobiEulerSixProduct :=
        jacobiAlternatingThetaProduct_pow_four_mul_theta_triangular
    _ = jacobiSignedCubeSeries ^ 2 :=
      JacobiCubeProduct.jacobiSignedCubeSeries_sq_eq_jacobiEulerSixProduct.symm
    _ = rationalIntegerThetaSeries * rationalTriangularThetaSeries +
        PowerSeries.C 4 * PowerSeries.X *
          (rationalIntegerThetaSeries *
              PowerSeries.derivative ℚ rationalTriangularThetaSeries -
            PowerSeries.derivative ℚ rationalIntegerThetaSeries *
              rationalTriangularThetaSeries) :=
      jacobiSignedCubeSeries_sq_eq_theta_wronskian
    _ = jacobiThetaProduct * jacobiTriangularProduct +
        PowerSeries.C 4 * PowerSeries.X *
          (jacobiThetaProduct *
              PowerSeries.derivative ℚ jacobiTriangularProduct -
            PowerSeries.derivative ℚ jacobiThetaProduct *
              jacobiTriangularProduct) := by
      rw [← jacobiThetaProduct_eq_rationalIntegerThetaSeries,
        ← JacobiTriangularProduct.jacobiTriangularProduct_eq_rationalTriangularThetaSeries]
    _ = (jacobiThetaProduct * jacobiTriangularProduct) *
        (1 + PowerSeries.C 4 * PowerSeries.X *
          jacobiLogDerivativeDifference) :=
      jacobi_cube_correction_factorization
    _ = (1 + PowerSeries.C 4 * PowerSeries.X *
          jacobiLogDerivativeDifference) *
        (jacobiThetaProduct * jacobiTriangularProduct) := by ring
end QEC.Coding.TannerLiftedProduct
