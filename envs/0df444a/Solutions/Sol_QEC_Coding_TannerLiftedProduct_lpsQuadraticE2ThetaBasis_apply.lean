-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticE2ThetaBasis_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:02:36.684033+00:00
-- url     : https://prove2.me/submissions/baa1d16d-1368-46ea-a61d-c9b3944bf0e1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (a : Fin 5) (z : ℍ) :
    lpsQuadraticE2ThetaBasis q hq2 a z=
      lpsQuadraticE2Dilate q (2^a.val) (pow_pos (by decide) _) z := rfl
end QEC.Coding.TannerLiftedProduct
