-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRatFuncToJ_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:40:52.833636+00:00
-- url     : https://prove2.me/submissions/fe95ff1c-4346-4915-87c5-daa890b5736b

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_TwoChartFiniteDimensionalBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalChartComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRatFuncToJ_polynomial

set_option autoImplicit false
open QEC.Coding.TannerLiftedProduct
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
noncomputable section
local notation "P" => Polynomial ℂ
local notation "J" => FractionRing P
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    lpsOriginalRatFuncToJ RatFunc.X = algebraMap P J Polynomial.X := by
  rw [← RatFunc.algebraMap_X]
  exact lpsOriginalRatFuncToJ_polynomial Polynomial.X
end QEC.Coding.TannerLiftedProduct
