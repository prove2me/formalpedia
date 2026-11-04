-- Prove2me | solution 1 for ThreeSum.HierarchyScales.allPrefixBoxes_envelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:34:33.943148+00:00
-- url     : https://prove2.me/submissions/a6439ed5-83d1-40da-ace6-b3af3173eec1

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Theorems.Thm_ThreeSum_HierarchyScales_terminalDepth_le_mu
import Definitions.Def_WeightedCache3SUM_Alias_808968550ac37650
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
theorem _root_.solution {n : ℕ} (hmu : 0 < mu n) :
    (allPrefixBoxes n : ℝ) ≤ hierarchyEnvelope (2 * E + 2 * bandShift - boxSaving) 0 n := by
  unfold allPrefixBoxes
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ j ∈ Finset.range (terminalDepth n + 1),
        Real.exp ((mu n : ℝ) * Real.log 2 * (2 * E + 2 * bandShift - boxSaving)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact Real.le_exp_of_log_le (prefixBoxes_log_bound hmu (by simpa using hj))
    _ = (terminalDepth n + 1 : ℝ) *
        Real.exp ((mu n : ℝ) * Real.log 2 * (2 * E + 2 * bandShift - boxSaving)) := by simp
    _ ≤ hierarchyEnvelope (2 * E + 2 * bandShift - boxSaving) 0 n := by
      simp only [hierarchyEnvelope, add_zero]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact_mod_cast Nat.add_le_add_right (terminalDepth_le_mu hmu) 1
end ThreeSum.HierarchyScales
