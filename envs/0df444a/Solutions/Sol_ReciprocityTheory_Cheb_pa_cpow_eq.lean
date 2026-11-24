-- Prove2me | solution 1 for ReciprocityTheory.Cheb.pa_cpow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:55.687846+00:00
-- url     : https://prove2.me/submissions/3a2bd34a-e5f6-4719-a691-489e31d915c1

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerLim
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeAsymp

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
theorem _root_.solution (n : ℕ) (s : ℝ) :
    ((n : ℂ) ^ (-(s : ℂ))) = (((n : ℝ) ^ (-s) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
  push_cast
  rfl
end ReciprocityTheory.Cheb
