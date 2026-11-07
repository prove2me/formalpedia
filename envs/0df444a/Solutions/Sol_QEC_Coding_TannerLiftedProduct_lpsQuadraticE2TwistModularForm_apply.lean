-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:57:42.814448+00:00
-- url     : https://prove2.me/submissions/c19c39cb-9ded-4092-94f3-76da93846a95

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (z : ℍ) :
    lpsQuadraticE2TwistModularForm q hq2 z=lpsQuadraticE2Twist q z := rfl
end QEC.Coding.TannerLiftedProduct
