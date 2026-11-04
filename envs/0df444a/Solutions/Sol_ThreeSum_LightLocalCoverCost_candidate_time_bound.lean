-- Prove2me | solution 1 for ThreeSum.LightLocalCoverCost.candidate_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:19:59.120205+00:00
-- url     : https://prove2.me/submissions/16f490f3-6369-436a-8cda-9c206acf98fb

import Definitions.Def_Submission_ThreeSum_LightLocalCoverLayout
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCost
import Theorems.Thm_ThreeSum_LightLocalCoverCost_hash_time_bound
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
theorem _root_.solution {L n p N B : ℕ}
    (hB : 1 ≤ B) (hL : L+1 ≤ B) (hn : n+1 ≤ B) (hp : p+1 ≤ B) (hN : N+1 ≤ B) :
    LightLocalCoverCandidate.time L n p N ≤ 5000*B^4 := by
  have hdecode : LightWeightDecode.time L N ≤ 600*B^2 := by
    calc
      _ ≤ 600*(L+1)*(N+1) := LightWeightDecode.time_bound L N
      _ ≤ 600*B*B := by gcongr
      _ = _ := by ring
  have hhash : LightHashHistogram.time L n p p ≤ 1000*B^3 := by
    calc
      _ ≤ 1000*(L+1)*(n+1)*(p+1) := hash_time_bound L n p
      _ ≤ 1000*B*B*B := by gcongr
      _ = _ := by ring
  have hn2 : n*n+1 ≤ B^2 := by
    have hm := Nat.pow_le_pow_left hn 2
    nlinarith
  have hp2 : p*p ≤ B^2 := by
    have hm := Nat.pow_le_pow_left hp 2
    nlinarith
  have hB2 : B ≤ B^2 := Nat.le_self_pow (by decide) B
  have hrest : L+n+p*p+1 ≤ 3*B^2 := by omega
  have hrow : LightLocalCoverRow.time L n p ≤ 1800*B^4 := by
    calc
      _ ≤ 600*(n*n+1)*(L+n+p*p+1) := LightLocalCoverRow.time_bound L n p
      _ ≤ 600*(B^2)*(3*B^2) := Nat.mul_le_mul (Nat.mul_le_mul_left 600 hn2) hrest
      _ = _ := by ring
  have hb24 := Nat.pow_le_pow_right hB (by decide : 2 ≤ 4)
  have hb34 := Nat.pow_le_pow_right hB (by decide : 3 ≤ 4)
  have hb4 : 1 ≤ B^4 := Nat.pow_pos (by omega)
  unfold LightLocalCoverCandidate.time
  omega
end ThreeSum.LightLocalCoverCost
