-- Prove2me | solution 1 for ThreeSum.LightLocalCoverResources.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:45:36.281702+00:00
-- url     : https://prove2.me/submissions/dfcfa46b-45a6-4eca-9fba-bdf8f789f408

import Definitions.Def_Submission_ThreeSum_LightLocalCoverSetup
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCost
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Theorems.Thm_ThreeSum_LightLocalCoverResources_setup_time_polynomial
import Definitions.Def_WeightedCache3SUM_Alias_f93cfd5252bad152
import Theorems.Thm_ThreeSum_LocalParameterBounds_pow_pos


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMagnitude
set_option maxHeartbeats 1800000
namespace ThreeSum.LightLocalCoverResources
theorem _root_.solution (h : ℕ) : LightLocalCoverSetup.time h ≤ envelope h := by
  have hs : 1 ≤ (h+1)^2 := Nat.pow_pos (by omega)
  calc
    _ ≤ 11000*(magnitude h)^5 := setup_time_polynomial (bounds h)
    _ ≤ 2^14*(magnitude h)^5 := Nat.mul_le_mul_right _ (by decide)
    _ = 2^(14+600000*(h+1)^2*5) := by rw [magnitude,← pow_mul,← pow_add]
    _ ≤ envelope h := Nat.pow_le_pow_right (by decide) (by omega)
end ThreeSum.LightLocalCoverResources
