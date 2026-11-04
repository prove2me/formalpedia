-- Prove2me | solution 1 for ThreeSum.MassScales.falseMajorant_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:52:45.543365+00:00
-- url     : https://prove2.me/submissions/f7924946-89a4-4008-b9b4-d6070eaa7c78

import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Definitions.Def_Submission_ThreeSum_MassScales
import Theorems.Thm_ThreeSum_MassScales_falseNumerator_eventually_pos
import Definitions.Def_WeightedCache3SUM_Alias_69e8853770c910e9
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Scales_radix_log_ratio_tendsto
import Theorems.Thm_ThreeSum_Scales_radix_pos
import Theorems.Thm_ThreeSum_Switch_mem_candidates
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
theorem _root_.solution (k : ℕ) :
    Tendsto (fun n : ℕ => Real.log (falseMajorant k n) / Real.log n) atTop
      (𝓝 (2 - (1 / 2 - bandShift) / 5)) := by
  have hh := (falseNumerator_log_rate k).sub radix_log_ratio_tendsto
  have hid : (2 + (E + bandShift) / 5) - (E + 1 / 2) / 5 =
      2 - (1 / 2 - bandShift) / 5 := by ring
  rw [hid] at hh
  apply hh.congr'
  filter_upwards [falseNumerator_eventually_pos k] with n hn
  have hN : (falseNumerator k n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hR : (radix n : ℝ) ≠ 0 := by exact_mod_cast (radix_pos n).ne'
  simp only [falseMajorant, Real.log_div hN hR, sub_div]
end ThreeSum.MassScales
