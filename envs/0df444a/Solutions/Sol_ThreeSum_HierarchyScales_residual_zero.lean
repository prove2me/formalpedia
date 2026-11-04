-- Prove2me | solution 1 for ThreeSum.HierarchyScales.residual_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:17:36.956483+00:00
-- url     : https://prove2.me/submissions/c41da6f1-cb85-4089-9d6f-f74012a1742d

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Switch_actual_totalSize
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
namespace ThreeSum.HierarchyScales
theorem _root_.solution (n : ℕ) : residualSize n 0 = mu n := by
  simp only [residualSize, Nat.sub_zero, actual_totalSize]
end ThreeSum.HierarchyScales
