-- Prove2me | solution 1 for ThreeSum.LightTernaryNearEnumeration.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:44:10.916821+00:00
-- url     : https://prove2.me/submissions/40cd3191-dd0d-47c6-bd7f-71500a957a49

import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumeration
import Theorems.Thm_ThreeSum_TernaryEnumeration_visits_le
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_visits_le


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryNearEnumeration
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryAddresses
open ThreeSum.TernaryNearEnumeration
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryNearEnumeration
theorem _root_.solution (qs : List ℕ) (D : ℕ) :
    time qs D ≤ 900*((qs.length+1)*(words qs D).length) :=
  Nat.mul_le_mul_left 900 (visits_le qs D)
end ThreeSum.LightTernaryNearEnumeration
