-- Prove2me | solution 1 for ThreeSum.LightCacheEnumeration.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:37:49.353133+00:00
-- url     : https://prove2.me/submissions/af46cb25-d986-433d-ada6-7d97803d53c4

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_LightEnumeration
import Theorems.Thm_ThreeSum_TernaryAddresses_visits_le_codes
import Theorems.Thm_ThreeSum_WeightedAddresses_visits_le_codes


set_option autoImplicit false
open ThreeSum ThreeSum.LightCacheEnumeration
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
open Light ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightCacheEnumeration
theorem _root_.solution (N T : ℕ) :
    time N T ≤ 300*((N+1)*(codes N T).length) := by
  exact Nat.mul_le_mul_left 300 (visits_le_codes N T)
end ThreeSum.LightCacheEnumeration
