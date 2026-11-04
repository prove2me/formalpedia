-- Prove2me | solution 1 for ThreeSum.HierarchyScales.initialCap_accepted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:46:32.593198+00:00
-- url     : https://prove2.me/submissions/08068524-6a7e-428a-a925-1bb548d04c74

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Theorems.Thm_ThreeSum_HierarchyScales_initialCap_bounds
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
namespace ThreeSum.HierarchyScales
theorem _root_.solution (J r : ℕ) : accepts J 0 r (initialCap r) := by
  have hh := Nat.mul_le_mul_right (r ^ 2) (initialCap_bounds r).1
  have hm := Nat.mul_le_mul_left (291 * J) hh
  unfold accepts cubicNumerator
  simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero]
  ring_nf at hm ⊢
  omega
end ThreeSum.HierarchyScales
