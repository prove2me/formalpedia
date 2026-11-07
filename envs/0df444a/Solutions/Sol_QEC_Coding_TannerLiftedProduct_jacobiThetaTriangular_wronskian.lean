-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobiThetaTriangular_wronskian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:55:03.731187+00:00
-- url     : https://prove2.me/submissions/97ece5b2-3aee-48c5-888c-bdadd0557a26

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_derivative_jacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_derivative_jacobiTriangularProduct

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    jacobiThetaProduct *
        PowerSeries.derivative ℚ jacobiTriangularProduct -
      PowerSeries.derivative ℚ jacobiThetaProduct *
        jacobiTriangularProduct =
      (jacobiThetaProduct * jacobiTriangularProduct) *
        jacobiLogDerivativeDifference := by
  rw [derivative_jacobiThetaProduct,
    derivative_jacobiTriangularProduct, jacobiLogDerivativeDifference]
  ring
end QEC.Coding.TannerLiftedProduct
