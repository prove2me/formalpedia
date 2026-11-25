-- Prove2me | solution 1 for ReciprocityTheory.Cheb.chebyshev_first_estimate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:07:33.194988+00:00
-- url     : https://prove2.me/submissions/ef751727-103d-442c-8235-85f3c48a5226

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerLim
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeSum
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeCont
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeAsymp
import Definitions.Def_ReciprocityTheory_Chebotarev_ChebyshevLambdaSubPsiBounded
import Theorems.Thm_ReciprocityTheory_Cheb_ehold_summable
import Theorems.Thm_ReciprocityTheory_Cheb_dedekindZeta_eq_tsum
import Theorems.Thm_ReciprocityTheory_Cheb_summable_prm_rpow


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
theorem _root_.solution : E1 := by
  refine ⟨fun E _ _ f hf s hs => (ehold_summable f hf hs).of_norm, fun E _ _ s hs => dedekindZeta_eq_tsum E hs,
    fun E _ _ s hs => summable_prm_rpow E hs⟩
end ReciprocityTheory.Cheb
