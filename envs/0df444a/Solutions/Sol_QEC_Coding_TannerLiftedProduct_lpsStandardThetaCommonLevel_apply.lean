-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsStandardThetaCommonLevel_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:23:03.28539+00:00
-- url     : https://prove2.me/submissions/1a8aeb23-c135-49ae-a836-2599d0b9b2a7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularTraceBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) (hq : 0<q) (z : ℍ) :
    lpsStandardThetaCommonLevel q hq z=lpsStandardTheta q z := rfl
end QEC.Coding.TannerLiftedProduct
