-- Prove2me | solution 1 for ThreeSum.LightLocalCoverResources.word_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:27:47.140872+00:00
-- url     : https://prove2.me/submissions/7547c78c-f4d4-4fa4-98be-5c3b38d3a1f6

import Definitions.Def_Submission_ThreeSum_LightLocalCoverSetup
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCost
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Definitions.Def_WeightedCache3SUM_Alias_5e8b98b2553608db
import Definitions.Def_WeightedCache3SUM_Alias_f93cfd5252bad152
import Theorems.Thm_ThreeSum_LocalParameterBounds_pow_pos


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMagnitude
set_option maxHeartbeats 1800000
namespace ThreeSum.LightLocalCoverResources
theorem _root_.solution (h : ℕ) : LightLocalCoverSetup.word h ≤ envelope h := by
  have hs : 1 ≤ (h+1)^2 := Nat.pow_pos (by omega)
  calc
    _ ≤ 2000*(magnitude h)^2 := word_polynomial (bounds h)
    _ ≤ 2^11*(magnitude h)^2 := Nat.mul_le_mul_right _ (by decide)
    _ = 2^(11+600000*(h+1)^2*2) := by rw [magnitude,← pow_mul,← pow_add]
    _ ≤ envelope h := Nat.pow_le_pow_right (by decide) (by omega)
end ThreeSum.LightLocalCoverResources
