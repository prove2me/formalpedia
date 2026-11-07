-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChi4PrimeE2TwistModularForm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:08:22.787254+00:00
-- url     : https://prove2.me/submissions/f6540536-b475-4d1f-8fd3-d713463f2ad9

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (z : ℍ) :
    lpsChi4PrimeE2TwistModularForm q hq2 z=lpsChi4PrimeE2Twist q z := rfl
end QEC.Coding.TannerLiftedProduct
