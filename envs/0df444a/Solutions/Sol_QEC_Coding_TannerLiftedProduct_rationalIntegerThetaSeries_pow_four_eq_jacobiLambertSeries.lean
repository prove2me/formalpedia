-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.rationalIntegerThetaSeries_pow_four_eq_jacobiLambertSeries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:09:16.899176+00:00
-- url     : https://prove2.me/submissions/9dabf36c-5298-4602-9ac9-f005a6b91940

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareIdentity
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiAlternatingThetaProduct_pow_four_eq_logDerivativeCorrection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_substNegX_jacobiAlternatingThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_substNegX_logDerivativeCorrection_eq_jacobiLambertSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiThetaProduct_eq_rationalIntegerThetaSeries


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    rationalIntegerThetaSeries ^ 4 = jacobiLambertSeries := by
  have h := congrArg substNegX
    jacobiAlternatingThetaProduct_pow_four_eq_logDerivativeCorrection
  rw [map_pow, substNegX_jacobiAlternatingThetaProduct,
    substNegX_logDerivativeCorrection_eq_jacobiLambertSeries] at h
  rw [← jacobiThetaProduct_eq_rationalIntegerThetaSeries]
  exact h
end QEC.Coding.TannerLiftedProduct
