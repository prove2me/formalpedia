-- Prove2me | solution 1 for ThreeSum.MassScales.wantedMajorant_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:48:42.168604+00:00
-- url     : https://prove2.me/submissions/a8c64fee-ba6f-41cc-8041-12346c66d0b2

import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Definitions.Def_Submission_ThreeSum_MassScales
import Theorems.Thm_ThreeSum_MassScales_wantedNumerator_pos
import Theorems.Thm_ThreeSum_MassScales_wantedNumerator_log_rate
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
theorem _root_.solution :
    Tendsto (fun n : ℕ => Real.log (wantedMajorant n) / Real.log n) atTop
      (𝓝 (2 - (1 / 2 + bandShift) / 5)) := by
  have hh := wantedNumerator_log_rate.sub radix_log_ratio_tendsto
  have hid : (2 + 2 * E / 5 - (E + bandShift) / 5) - (E + 1 / 2) / 5 =
      2 - (1 / 2 + bandShift) / 5 := by ring
  rw [hid] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hN : (wantedNumerator n : ℝ) ≠ 0 := by exact_mod_cast (wantedNumerator_pos (by omega : 0 < n)).ne'
  have hR : (radix n : ℝ) ≠ 0 := by exact_mod_cast (radix_pos n).ne'
  simp only [wantedMajorant, Real.log_div hN hR, sub_div]
end ThreeSum.MassScales
