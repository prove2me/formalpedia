-- Prove2me | solution 1 for ThreeSum.TrimScales.localBucketCap_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:24:13.430032+00:00
-- url     : https://prove2.me/submissions/4f824c9f-6e51-4723-96b6-56dd182cb979

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
import Theorems.Thm_ThreeSum_TrimScales_vertexLoad_pos
import Theorems.Thm_ThreeSum_TrimScales_vertexLoad_log_rate
import Theorems.Thm_ThreeSum_TrimScales_localBucketCap_ge_load
import Theorems.Thm_ThreeSum_TrimScales_localBucketCap_pos
import Theorems.Thm_ThreeSum_TrimScales_localBucketCap_eventually_le_nine_load
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
    Tendsto (fun h : ℕ => Real.log (LocalCoverBounds.localBucketCap h : ℝ) /
      ((2 * h : ℝ) * Real.log 2)) atTop (𝓝 (Parameters.kappa / 2)) := by
  have herr : Tendsto (fun h : ℕ => Real.log 9 / ((2 * h : ℝ) * Real.log 2))
      atTop (𝓝 0) := by
    have hi := (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hi.const_mul (Real.log 9 / (2 * Real.log 2))
  have hu := vertexLoad_log_rate.add herr
  simp only [add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' vertexLoad_log_rate hu
  · filter_upwards [] with h
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (vertexLoad_pos h) (localBucketCap_ge_load h)) (by positivity)
  · filter_upwards [localBucketCap_eventually_le_nine_load] with h hh
    have hc : (0 : ℝ) < LocalCoverBounds.localBucketCap h := by exact_mod_cast localBucketCap_pos h
    have hlog := Real.log_le_log hc hh
    rw [Real.log_mul (by norm_num : (9 : ℝ) ≠ 0) (vertexLoad_pos h).ne'] at hlog
    have hd := div_le_div_of_nonneg_right hlog (by positivity :
      (0 : ℝ) ≤ (2 * h : ℝ) * Real.log 2)
    simpa only [add_div, add_comm] using hd
end ThreeSum.TrimScales
