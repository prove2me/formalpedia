-- Prove2me | solution 1 for ThreeSum.HierarchyScales.bandCount_ge_unrounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:46:34.741826+00:00
-- url     : https://prove2.me/submissions/02b2bfa9-0ef6-46f4-bd5e-eab96e0500f3

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Theorems.Thm_ThreeSum_BandScales_bandSize_pos
import Theorems.Thm_ThreeSum_CostLedger_bandCount_mul_bounds
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
theorem _root_.solution (n : ℕ) : unroundedBandCount n ≤ (bandCount n : ℝ) := by
  have hb : (0 : ℝ) < BandScales.bandSize n := by exact_mod_cast BandScales.bandSize_pos n
  rw [unroundedBandCount, div_le_iff₀ hb]
  have hn : (n : ℝ) ≤ (BandScales.bandSize n : ℝ) * bandCount n :=
    by exact_mod_cast (bandCount_mul_bounds n).1
  simpa only [mul_comm] using hn
end ThreeSum.HierarchyScales
