-- Prove2me | solution 1 for ReciprocityTheory.Cheb.proper_base_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:27:55.446701+00:00
-- url     : https://prove2.me/submissions/d89d5d8e-dc86-44bd-8eae-4649a1b19d3d

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerLim
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeSum
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeCont
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeAsymp
import Definitions.Def_ReciprocityTheory_Chebotarev_ChebyshevLambdaSubPsiBounded
import Theorems.Thm_ReciprocityTheory_Cheb_chebyshev_second_estimate

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
theorem _root_.solution : E2 := chebyshev_second_estimate
end ReciprocityTheory.Cheb
