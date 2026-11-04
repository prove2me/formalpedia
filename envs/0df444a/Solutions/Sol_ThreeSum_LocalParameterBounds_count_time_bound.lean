-- Prove2me | solution 1 for ThreeSum.LocalParameterBounds.count_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:04:42.0682+00:00
-- url     : https://prove2.me/submissions/4ebee9b0-4d0f-4ac2-8077-a1f8f598bd05

import Definitions.Def_Submission_ThreeSum_LightLocalParameters
import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Theorems.Thm_ThreeSum_LocalParameterBounds_width_bound
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_ThreeSum_LightLocalCounts_time_bound
import Theorems.Thm_ThreeSum_LightResidueHistogram_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_ea9db4f154655ba6
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LocalParameterBounds
open LocalCoverBounds
set_option maxHeartbeats 1000000
namespace ThreeSum.LocalParameterBounds
theorem _root_.solution (h : ℕ) : LightLocalCounts.time h ≤ 2^(2*h+31) := by
  calc
    LightLocalCounts.time h ≤ 1700*(512*h+1)^2 := LightLocalCounts.time_bound h
    _ ≤ 2^11*(2^(h+10))^2 := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left (width_bound h) 2)
    _ = 2^(2*h+31) := by rw [← pow_mul,← pow_add]; congr 1 <;> omega
end ThreeSum.LocalParameterBounds
