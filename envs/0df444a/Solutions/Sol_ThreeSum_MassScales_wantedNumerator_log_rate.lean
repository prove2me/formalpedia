-- Prove2me | solution 1 for ThreeSum.MassScales.wantedNumerator_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:46:13.387254+00:00
-- url     : https://prove2.me/submissions/65c984f5-6378-4700-88c1-f2323011d159

import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Definitions.Def_Submission_ThreeSum_MassScales
import Theorems.Thm_ThreeSum_MassScales_scheduleCount_pos
import Theorems.Thm_ThreeSum_MassScales_bandCount_pos
import Theorems.Thm_ThreeSum_MassScales_nat_log_rate_const
import Theorems.Thm_ThreeSum_MassScales_nat_log_rate_mul
import Theorems.Thm_ThreeSum_MassScales_nat_log_rate_pow
import Theorems.Thm_ThreeSum_MassScales_bandSize_log_rate_shift
import Theorems.Thm_ThreeSum_BandScales_bandSize_pos
import Theorems.Thm_ThreeSum_BandScales_typedOutputs_pos
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Definitions.Def_WeightedCache3SUM_Alias_79670fd38525811b
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_e8286cd6503d6aa9
import Theorems.Thm_ThreeSum_Switch_mem_candidates
import Theorems.Thm_ThreeSum_TrimScales_scheduleCount_log_rate
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.Switch.mem_candidates



set_option autoImplicit false
open ThreeSum ThreeSum.MassScales
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.CostLedger ThreeSum.HierarchyScales
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace ThreeSum.MassScales
theorem _root_.solution :
    Tendsto (fun n : ℕ => Real.log (wantedNumerator n : ℝ) / Real.log n) atTop
      (𝓝 (2 + 2 * E / 5 - (E + bandShift) / 5)) := by
  have h1 := nat_log_rate_mul (nat_log_rate_const 9) scheduleCount_log_rate (by
    filter_upwards [] with n
    exact ⟨by norm_num, scheduleCount_pos n⟩)
  have h2 := nat_log_rate_mul h1 typedOutputs_log_ratio_tendsto (by
    filter_upwards [] with n
    exact ⟨Nat.mul_pos (by norm_num) (scheduleCount_pos n), typedOutputs_pos n⟩)
  have h3 := nat_log_rate_mul h2 (nat_log_rate_pow bandCount_log_rate 2) (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact ⟨Nat.mul_pos (Nat.mul_pos (by norm_num) (scheduleCount_pos n)) (typedOutputs_pos n),
      Nat.pow_pos (bandCount_pos (by omega))⟩)
  have h4 := nat_log_rate_mul h3 bandSize_log_rate_shift (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    refine ⟨?_, bandSize_pos n⟩
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) (scheduleCount_pos n))
      (typedOutputs_pos n)) (Nat.pow_pos (bandCount_pos (by omega))))
  convert h4 using 1 <;> simp only [wantedNumerator, Nat.cast_ofNat] <;> ring
end ThreeSum.MassScales
