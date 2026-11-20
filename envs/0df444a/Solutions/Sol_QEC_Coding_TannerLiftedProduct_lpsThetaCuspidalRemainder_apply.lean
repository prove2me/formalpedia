-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaCuspidalRemainder_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:25:15.46618+00:00
-- url     : https://prove2.me/submissions/dc405282-fc77-4847-be8f-5d156f57f0f1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularTraceBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) (z : ℍ) :
    lpsThetaCuspidalRemainder q hq4 z=lpsStandardTheta q z-
      lpsThetaEisensteinCorrection q (by intro h;subst q;norm_num at hq4) z := rfl
end QEC.Coding.TannerLiftedProduct
