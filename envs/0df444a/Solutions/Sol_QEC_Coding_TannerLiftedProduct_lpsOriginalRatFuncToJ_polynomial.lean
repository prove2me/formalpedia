-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRatFuncToJ_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:37:12.369834+00:00
-- url     : https://prove2.me/submissions/64affb89-7c53-41d1-9000-a92332ad890c

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_TwoChartFiniteDimensionalBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalChartComparison

set_option autoImplicit false
open QEC.Coding.TannerLiftedProduct
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
noncomputable section
local notation "P" => Polynomial ℂ
local notation "J" => FractionRing P
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : P) :
    lpsOriginalRatFuncToJ (algebraMap P (RatFunc ℂ) p) = algebraMap P J p :=
  (IsLocalization.algEquiv (nonZeroDivisors P) (RatFunc ℂ) J).commutes p
end QEC.Coding.TannerLiftedProduct
