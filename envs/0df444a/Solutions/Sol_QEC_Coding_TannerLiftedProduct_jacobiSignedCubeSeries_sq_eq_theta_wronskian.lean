-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobiSignedCubeSeries_sq_eq_theta_wronskian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:24:20.906061+00:00
-- url     : https://prove2.me/submissions/95e3907b-34d6-4268-a6eb-8d8391b6a858

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiParityReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiSignedCubeSeries_sq_eq_weighted_reindex
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_derivative_rationalTriangularThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiWeightedSquareSeries_eq_derivative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiWeightedTriangularSeries_eq_derivative


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    jacobiSignedCubeSeries ^ 2 =
      rationalIntegerThetaSeries * rationalTriangularThetaSeries +
        PowerSeries.C 4 * PowerSeries.X *
          (rationalIntegerThetaSeries *
              PowerSeries.derivative ℚ rationalTriangularThetaSeries -
            PowerSeries.derivative ℚ rationalIntegerThetaSeries *
              rationalTriangularThetaSeries) := by
  rw [jacobiSignedCubeSeries_sq_eq_weighted_reindex,
    jacobiWeightedTriangularSeries_eq_derivative,
    jacobiWeightedSquareSeries_eq_derivative,
    derivative_rationalTriangularThetaSeries,
    rationalTriangularThetaSeries]
  ring
end QEC.Coding.TannerLiftedProduct
