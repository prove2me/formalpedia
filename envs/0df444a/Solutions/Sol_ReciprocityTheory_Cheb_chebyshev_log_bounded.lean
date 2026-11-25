-- Prove2me | solution 1 for ReciprocityTheory.Cheb.chebyshev_log_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:04:48.911532+00:00
-- url     : https://prove2.me/submissions/5465e615-3c08-4411-a29d-9039269399e1

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerLim
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeSum
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeCont
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeAsymp
import Definitions.Def_ReciprocityTheory_Chebotarev_ChebyshevLambdaSubPsiBounded
import Theorems.Thm_ReciprocityTheory_Cheb_pe_log_bdd


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
theorem _root_.solution : faceMap_castSucc_comp_eq_succ := pe_log_bdd
end ReciprocityTheory.Cheb
