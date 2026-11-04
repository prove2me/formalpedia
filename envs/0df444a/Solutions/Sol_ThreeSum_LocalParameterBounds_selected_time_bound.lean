-- Prove2me | solution 1 for ThreeSum.LocalParameterBounds.selected_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:04:43.171307+00:00
-- url     : https://prove2.me/submissions/c04263dd-dc17-4b61-a6ad-deead6cbc505

import Definitions.Def_Submission_ThreeSum_LightLocalParameters
import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Theorems.Thm_ThreeSum_LocalParameterBounds_pow_pos
import Theorems.Thm_ThreeSum_LocalParameterBounds_threshold_bound
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
theorem _root_.solution (h : ℕ) :
    LightSelectedPrime.time (localThreshold h) ≤ 2^(1542*h+19) := by
  have ht := threshold_bound h
  have hx := pow_pos (514*h)
  have ha : localThreshold h+2 ≤ 2^(514*h+2) := by
    rw [pow_add]
    norm_num
    omega
  calc
    _ ≤ 6000*(localThreshold h+2)^3 := LightSelectedPrime.time_bound _
    _ ≤ 2^13*(2^(514*h+2))^3 := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left ha 3)
    _ = 2^(1542*h+19) := by rw [← pow_mul,← pow_add]; congr 1 <;> omega
end ThreeSum.LocalParameterBounds
