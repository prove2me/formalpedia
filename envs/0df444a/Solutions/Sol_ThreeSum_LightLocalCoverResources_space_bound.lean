-- Prove2me | solution 1 for ThreeSum.LightLocalCoverResources.space_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:27:48.355215+00:00
-- url     : https://prove2.me/submissions/5ae2942f-fa52-4c3a-9527-ff36ecb409d8

import Definitions.Def_Submission_ThreeSum_LightLocalCoverSetup
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCost
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Definitions.Def_WeightedCache3SUM_Alias_e594851d6b44532e
import Definitions.Def_WeightedCache3SUM_Alias_f93cfd5252bad152
import Theorems.Thm_ThreeSum_LocalParameterBounds_pow_pos


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMagnitude
set_option maxHeartbeats 1800000
namespace ThreeSum.LightLocalCoverResources
theorem _root_.solution (base h : ℕ) : space base h ≤ base+envelope h := by
  have hs : 1 ≤ (h+1)^2 := Nat.pow_pos (by omega)
  apply (space_polynomial (bounds h) base).trans
  apply Nat.add_le_add_left
  calc
    20*(magnitude h)^3 ≤ 2^5*(magnitude h)^3 := Nat.mul_le_mul_right _ (by decide)
    _ = 2^(5+600000*(h+1)^2*3) := by rw [magnitude,← pow_mul,← pow_add]
    _ ≤ envelope h := Nat.pow_le_pow_right (by decide) (by omega)
end ThreeSum.LightLocalCoverResources
