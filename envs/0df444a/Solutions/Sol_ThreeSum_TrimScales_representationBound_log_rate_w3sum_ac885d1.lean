-- Prove2me | solution 1 for ThreeSum.TrimScales.representationBound_log_rate_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:32:27.930881+00:00
-- url     : https://prove2.me/submissions/bf360eb4-ae0f-4054-800c-72bc962aa86e

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
import Theorems.Thm_ThreeSum_TrimScales_localBucketCap_pos
import Theorems.Thm_ThreeSum_TrimScales_trimMultiplicity_log_rate
import Theorems.Thm_ThreeSum_TrimScales_localLength_pos
import Theorems.Thm_ThreeSum_TrimScales_scheduleCount_log_rate
import Theorems.Thm_ThreeSum_TrimScales_representationBound_eq
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.TrimScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section
namespace ThreeSum.TrimScales
theorem _root_.solution :
    Tendsto (fun n : ℕ => Real.log (representationBound n : ℝ) / Real.log n) atTop
      (𝓝 (Parameters.kappa / 5)) := by
  have h := scheduleCount_log_rate.add trimMultiplicity_log_rate
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [] with n
  have hs : (0 : ℝ) < scheduleCount n := by
    exact_mod_cast (Nat.pow_pos (localLength_pos (microHalf (inputBits n))) :
      0 < scheduleCount n)
  have ht : (0 : ℝ) < trimMultiplicity n := by
    exact_mod_cast (Nat.pow_pos (localBucketCap_pos (microHalf (inputBits n))) :
      0 < trimMultiplicity n)
  rw [representationBound_eq, Nat.cast_mul, Real.log_mul hs.ne' ht.ne', add_div]
end ThreeSum.TrimScales
