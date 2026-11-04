-- Prove2me | solution 1 for ThreeSum.LightLocalCoverCost.host_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:29:24.193761+00:00
-- url     : https://prove2.me/submissions/20de44a5-2116-4f16-9ab9-feb323c0a89c

import Definitions.Def_Submission_ThreeSum_LightLocalCoverLayout
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCost
import Theorems.Thm_ThreeSum_LightLocalCoverCost_greedy_time_bound
import Theorems.Thm_ThreeSum_LightLocalCoverCost_matrix_time_bound
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
    LightLocalCoverHost.time h ≤ 8000*B^5 := by
  have hm := matrix_time_bound hB hL hn hp hN
  have hp2 : cols h+1 ≤ B^2 := by
    have hs := Nat.pow_le_pow_left hp 2
    unfold cols
    nlinarith
  have hg : LightCoverGreedy.time (rows h) (cols h) (scheduleSize h) ≤ 1000*B^4 := by
    calc
      _ ≤ 1000*(rows h+1)*(cols h+1)*(scheduleSize h+1) := greedy_time_bound _ _ _
      _ ≤ 1000*B*(B^2)*B := by gcongr
      _ = _ := by ring
  have hh : LightWeightGather.time (scheduleSize h) (2*(512*h)) ≤ 260*B^2 := by
    calc
      _ ≤ 130*(scheduleSize h+1)*(2*(512*h)+1) := LightWeightGather.time_bound _ _
      _ ≤ 130*B*(2*B) := Nat.mul_le_mul (Nat.mul_le_mul_left 130 hT) (by omega)
      _ = _ := by ring
  have hb25 := Nat.pow_le_pow_right hB (by decide : 2 ≤ 5)
  have hb45 := Nat.pow_le_pow_right hB (by decide : 4 ≤ 5)
  have hb5 : 1 ≤ B^5 := Nat.pow_pos (by omega)
  unfold LightLocalCoverHost.time
  change LightLocalCoverMatrix.time (512*h) (vertices h) (localPrime h) (rows h)+
    LightCoverGreedy.time (rows h) (cols h) (scheduleSize h)+
    LightWeightGather.time (scheduleSize h) (2*(512*h))+200 ≤ _
  omega
end ThreeSum.LightLocalCoverCost
