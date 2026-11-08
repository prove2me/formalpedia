-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsE2DifferenceModularForm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:00:02.380194+00:00
-- url     : https://prove2.me/submissions/0b22c7d5-bb5f-476b-a4e6-04e83b0bbd98

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (m : ℕ) (hm : 0 < m) (z : ℍ) :
    lpsE2DifferenceModularForm m hm z=lpsE2Difference m hm z := rfl
end QEC.Coding.TannerLiftedProduct
