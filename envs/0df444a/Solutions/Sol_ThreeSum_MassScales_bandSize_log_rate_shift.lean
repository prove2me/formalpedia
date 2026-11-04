-- Prove2me | solution 1 for ThreeSum.MassScales.bandSize_log_rate_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:31:23.801809+00:00
-- url     : https://prove2.me/submissions/2c958d41-1a69-403c-85e2-edfbda587073

import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Definitions.Def_Submission_ThreeSum_MassScales
import Definitions.Def_WeightedCache3SUM_Alias_9e2ce7e309d596ff
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
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
    Tendsto (fun n : ℕ => Real.log (bandSize n : ℝ) / Real.log n) atTop
      (𝓝 ((E + bandShift) / 5)) := by
  simpa only [bandShift, sub_eq_add_neg] using BandScales.bandSize_log_rate
end ThreeSum.MassScales
