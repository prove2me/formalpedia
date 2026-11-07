-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsQuadraticE2TwistModularForm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:58:42.653992+00:00
-- url     : https://prove2.me/submissions/d643a98c-8c71-43a6-aee8-2b71f867bcdd

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_coeff_qExpansion


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsQuadraticE2TwistModularForm q hq2)) =
      -24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsQuadraticE2Character q (n:ZMod q) :=
  lpsQuadraticE2Twist_coeff_qExpansion q hq2 n
end QEC.Coding.TannerLiftedProduct
