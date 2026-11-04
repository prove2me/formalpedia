-- Prove2me | solution 1 for ThreeSum.LightLocalCoverCost.build_time_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:33:41.182254+00:00
-- url     : https://prove2.me/submissions/9d6d7dac-c3d7-41f3-9ea8-cc74356621bd

import Definitions.Def_Submission_ThreeSum_LightLocalCoverLayout
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCost
import Theorems.Thm_ThreeSum_LightLocalCoverCost_mask_table_time_bound
import Theorems.Thm_ThreeSum_LightLocalCoverCost_host_time_bound
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Theorems.Thm_ThreeSum_LightLocalCounts_time_bound
import Theorems.Thm_ThreeSum_LightLocalCoverRow_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound
import Theorems.Thm_ThreeSum_LightPairFlags_time_bound
import Theorems.Thm_ThreeSum_LightResidueHistogram_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_ea9db4f154655ba6
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound
import Theorems.Thm_ThreeSum_LightWeightDecode_time_bound
import Theorems.Thm_ThreeSum_LightWeightGather_time_bound
import Theorems.Thm_ThreeSum_LocalParameterBounds_pow_pos
import Definitions.Def_WeightedCache3SUM_Alias_e3ac3137889c3add


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverCost
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverLayout
set_option maxHeartbeats 1500000
namespace ThreeSum.LightLocalCoverCost
theorem _root_.solution {h B : ℕ}
    (hB : 1 ≤ B) (hL : 512*h+1 ≤ B) (hn : vertices h+1 ≤ B)
    (hp : localPrime h+1 ≤ B) (hN : rows h+1 ≤ B) (hT : scheduleSize h+1 ≤ B) :
    LightLocalCoverBuild.time h ≤ 10000*B^5 := by
  have hc := host_time_bound hB hL hn hp hN hT
  have he : LightSubsetEnumerationSetup.time (512*h) h ≤ 800*B^2 := by
    calc
      _ ≤ 800*(512*h+1)*((512*h).choose h+1) := LightSubsetEnumerationSetup.time_bound _ _
      _ ≤ 800*B*B := Nat.mul_le_mul (Nat.mul_le_mul_left 800 hL) hn
      _ = _ := by ring
  have hb : LightMaskBitTable.time (512*h) (vertices h) ≤ 400*B^3 := by
    calc
      _ ≤ 400*(vertices h+1)*(512*h+1)^2 := mask_table_time_bound _ _
      _ ≤ 400*B*(B^2) := by gcongr
      _ = _ := by ring
  have hb25 := Nat.pow_le_pow_right hB (by decide : 2 ≤ 5)
  have hb35 := Nat.pow_le_pow_right hB (by decide : 3 ≤ 5)
  have hb5 : 1 ≤ B^5 := Nat.pow_pos (by omega)
  unfold LightLocalCoverBuild.time
  change LightSubsetEnumerationSetup.time (512*h) h+
    LightMaskBitTable.time (512*h) (vertices h)+LightLocalCoverHost.time h+200 ≤ _
  omega
end ThreeSum.LightLocalCoverCost
