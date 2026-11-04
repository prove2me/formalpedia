-- Prove2me | solution 1 for ThreeSum.LightWeightedNearEnumeration.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:43:17.816287+00:00
-- url     : https://prove2.me/submissions/25318f76-1810-48b2-bbca-c0b8f37ce127

import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration
import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_LightNearEnumeration
import Theorems.Thm_ThreeSum_TernaryEnumeration_visits_le
import Theorems.Thm_ThreeSum_WeightedEnumeration_visits_le
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_visits_le


set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedNearEnumeration
open Light ThreeSum.LightSubsetAddress ThreeSum.WeightedAddresses
open ThreeSum.WeightedEnumeration (digitCost)
open ThreeSum.WeightedNearEnumeration
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightWeightedNearEnumeration
theorem _root_.solution (qs : List ℕ) (D : ℕ) :
    time qs D ≤ 900*((qs.length+1)*(words qs D).length) :=
  Nat.mul_le_mul_left 900 (visits_le qs D)
end ThreeSum.LightWeightedNearEnumeration
