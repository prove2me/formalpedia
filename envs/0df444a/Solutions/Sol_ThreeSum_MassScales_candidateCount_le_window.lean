-- Prove2me | solution 1 for ThreeSum.MassScales.candidateCount_le_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:47:46.78868+00:00
-- url     : https://prove2.me/submissions/fc90a35c-8275-43eb-bd21-7f4b45238784

import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Definitions.Def_Submission_ThreeSum_MassScales
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
theorem _root_.solution (n : ℕ) : candidateCount n ≤ 4 * primeWindow n := by
  unfold candidateCount PrimeDensity.candidates
  calc
    _ ≤ (Nat.primesLE (4 * primeWindow n)).card := Finset.card_le_card Finset.sdiff_subset
    _ ≤ 4 * primeWindow n := by
      rw [Nat.primesLE_eq_filter_Ioc_zero]
      exact (Finset.card_filter_le _ _).trans_eq (by simp)
end ThreeSum.MassScales
