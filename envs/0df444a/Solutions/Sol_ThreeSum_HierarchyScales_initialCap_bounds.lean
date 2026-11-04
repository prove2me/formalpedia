-- Prove2me | solution 1 for ThreeSum.HierarchyScales.initialCap_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:12:51.776051+00:00
-- url     : https://prove2.me/submissions/89fe7ded-d2bb-47d0-a743-6a57eb25432c

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
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
theorem _root_.solution (r : ℕ) : r ≤ 25 * initialCap r ∧ 25 * initialCap r < r + 25 := by
  constructor
  · exact (ceilDiv_le_iff_le_mul (a := 25) (b := r)
      (c := initialCap r) (by norm_num)).mp le_rfl
  · have h := Nat.div_mul_le_self (r + 25 - 1) 25
    simp only [initialCap, Nat.ceilDiv_eq_add_pred_div]
    omega
end ThreeSum.HierarchyScales
