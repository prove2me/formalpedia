-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticE2DilateModularForm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:01:35.784998+00:00
-- url     : https://prove2.me/submissions/849959cb-d4c8-4c77-a56c-8dea9196e06c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (m : ℕ) (hm : 0 < m) (z : ℍ) :
    lpsQuadraticE2DilateModularForm q hq2 m hm z=lpsQuadraticE2Dilate q m hm z := rfl
end QEC.Coding.TannerLiftedProduct
