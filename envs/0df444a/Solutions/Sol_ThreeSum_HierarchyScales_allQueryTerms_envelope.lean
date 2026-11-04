-- Prove2me | solution 1 for ThreeSum.HierarchyScales.allQueryTerms_envelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:34:35.300969+00:00
-- url     : https://prove2.me/submissions/e17f616a-3992-49cb-bdd8-2bd4cb290858

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Theorems.Thm_ThreeSum_HierarchyScales_terminalDepth_le_mu
import Definitions.Def_WeightedCache3SUM_Alias_d8086ee8a9c40c3f
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
    (allQueryTerms n : ℝ) ≤
      hierarchyEnvelope (entropyRatio * (1 + boxSaving - 2 * bandShift))
        (9 * entropyRatio * Real.log 2) n := by
  unfold allQueryTerms
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ j ∈ Finset.range (terminalDepth n + 1),
        Real.exp ((mu n : ℝ) * Real.log 2 *
          (entropyRatio * (1 + boxSaving - 2 * bandShift)) + 9 * entropyRatio * Real.log 2) := by
      apply Finset.sum_le_sum
      intro j hj
      exact Real.le_exp_of_log_le (queryTerms_log_bound hmu (by simpa using hj))
    _ = (terminalDepth n + 1 : ℝ) *
        Real.exp ((mu n : ℝ) * Real.log 2 *
          (entropyRatio * (1 + boxSaving - 2 * bandShift)) + 9 * entropyRatio * Real.log 2) := by simp
    _ ≤ hierarchyEnvelope (entropyRatio * (1 + boxSaving - 2 * bandShift))
        (9 * entropyRatio * Real.log 2) n := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact_mod_cast Nat.add_le_add_right (terminalDepth_le_mu hmu) 1
end ThreeSum.HierarchyScales
