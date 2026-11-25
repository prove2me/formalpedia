-- Prove2me | solution 1 for ReciprocityTheory.Cheb.smoothMap_seminorm_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:03:32.608797+00:00
-- url     : https://prove2.me/submissions/0ba88041-25f8-4fb4-a1a7-f30dc3cbbb41

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerLim
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeSum
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeCont
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeAsymp
import Definitions.Def_ReciprocityTheory_Chebotarev_ChebyshevLambdaSubPsiBounded
import Theorems.Thm_P2M_ReciprocityTheory_Cheb_smoothMap_seminorm_bound__39c12cba5872


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution : SmoothMapSeminormBound := smoothMap_seminorm_bound'
end ReciprocityTheory.Cheb
