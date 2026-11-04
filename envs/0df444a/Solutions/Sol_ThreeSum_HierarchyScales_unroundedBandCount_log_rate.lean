-- Prove2me | solution 1 for ThreeSum.HierarchyScales.unroundedBandCount_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:31:30.597846+00:00
-- url     : https://prove2.me/submissions/62bb02dc-4b02-4885-b706-ff6dae027f35

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Definitions.Def_WeightedCache3SUM_Alias_9e2ce7e309d596ff
import Theorems.Thm_ThreeSum_BandScales_bandSize_pos
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Switch_mem_candidates
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.Switch.mem_candidates



set_option autoImplicit false
open ThreeSum ThreeSum.HierarchyScales
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch ThreeSum.CostLedger
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace ThreeSum.HierarchyScales
theorem _root_.solution :
    Tendsto (fun n : ℕ => Real.log (unroundedBandCount n) / Real.log n) atTop
      (𝓝 (1 - (E + bandShift) / 5)) := by
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hh := hone.sub BandScales.bandSize_log_rate
  change Tendsto (fun n : ℕ => (1 : ℝ) - Real.log (BandScales.bandSize n : ℝ) / Real.log n)
    atTop (𝓝 (1 - (E - 1 / 20) / 5)) at hh
  change Tendsto _ _ (𝓝 (1 - (E - 1 / 20) / 5))
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hbR : (BandScales.bandSize n : ℝ) ≠ 0 := by exact_mod_cast (BandScales.bandSize_pos n).ne'
  have hlog : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
  simp only [unroundedBandCount, Real.log_div hnR hbR, sub_div, div_self hlog]
end ThreeSum.HierarchyScales
