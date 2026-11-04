-- Prove2me | solution 1 for ThreeSum.CostLedger.prefixChoices_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:13:29.097672+00:00
-- url     : https://prove2.me/submissions/f6a4ad25-c56b-4b8b-a18a-f364da7dfb15

import Definitions.Def_Submission_ThreeSum_Switch
import Mathlib.Tactic.LinearCombination
import Definitions.Def_Submission_ThreeSum_CostLedger
import Theorems.Thm_ThreeSum_CostLedger_microOutputs_pos
import Theorems.Thm_ThreeSum_CostLedger_microPartitions_pos
import Theorems.Thm_ThreeSum_CostLedger_microOutputs_log_bound
import Theorems.Thm_ThreeSum_CostLedger_microPartitions_log_bound
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Switch_mem_candidates
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.Switch.mem_candidates



set_option autoImplicit false
open ThreeSum ThreeSum.CostLedger
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch
open scoped Topology BigOperators
set_option maxHeartbeats 400000
noncomputable section
namespace ThreeSum.CostLedger
theorem _root_.solution {n j : ℕ} (hmu : 0 < mu n) :
    Real.log (prefixChoices n j : ℝ) ≤
      (j : ℝ) * muZero n * Real.log 2 * (2 * E + 1) := by
  have hM : (microOutputs n : ℝ) ≠ 0 := by exact_mod_cast (microOutputs_pos n).ne'
  have hG : (microPartitions n : ℝ) ≠ 0 := by exact_mod_cast (microPartitions_pos n).ne'
  simp only [prefixChoices, Nat.cast_pow, Nat.cast_mul, Real.log_pow, Real.log_mul hM hG]
  have hsum := add_le_add (microOutputs_log_bound hmu) (microPartitions_log_bound n)
  have hmul := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (α := ℝ) j)
  nlinarith
end ThreeSum.CostLedger
