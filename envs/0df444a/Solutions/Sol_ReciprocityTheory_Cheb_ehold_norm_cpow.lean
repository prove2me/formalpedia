-- Prove2me | solution 1 for ReciprocityTheory.Cheb.ehold_norm_cpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:55.105689+00:00
-- url     : https://prove2.me/submissions/b7c31252-9e8a-42c8-9619-c1d21d98e5bc

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerLim
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeSum
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeCont
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeAsymp
import Definitions.Def_ReciprocityTheory_Chebotarev_ChebyshevLambdaSubPsiBounded

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
theorem _root_.solution (n : ℕ) {s : ℝ} (hs : 1 < s) : ‖((n : ℂ) ^ (-(s : ℂ)))‖ = (n : ℝ) ^ (-s) := by
  rw [Complex.norm_natCast_cpow_of_re_ne_zero n (by simp; linarith)]
  simp
end ReciprocityTheory.Cheb
