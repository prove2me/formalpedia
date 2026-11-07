-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChi4E2TwistModularForm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:42:59.222285+00:00
-- url     : https://prove2.me/submissions/f40b7288-b61d-464c-a713-cfed6c2cbb76

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (z : ℍ) : lpsChi4E2TwistModularForm z=lpsChi4E2Twist z := rfl
end QEC.Coding.TannerLiftedProduct
