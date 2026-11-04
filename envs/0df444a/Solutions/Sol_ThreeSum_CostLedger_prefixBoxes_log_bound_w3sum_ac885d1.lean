-- Prove2me | solution 1 for ThreeSum.CostLedger.prefixBoxes_log_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:29:19.332201+00:00
-- url     : https://prove2.me/submissions/9cc6e1e0-37af-4686-bf64-9942e8793586

import Definitions.Def_Submission_ThreeSum_Switch
import Mathlib.Tactic.LinearCombination
import Definitions.Def_Submission_ThreeSum_CostLedger
import Theorems.Thm_ThreeSum_CostLedger_prefixChoices_pos
import Theorems.Thm_ThreeSum_CostLedger_suffixBoxes_pos
import Theorems.Thm_ThreeSum_CostLedger_prefixChoices_log_bound
import Theorems.Thm_ThreeSum_CostLedger_suffixBoxes_log_bound
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Definitions.Def_WeightedCache3SUM_Alias_99dfc3473a1cfe41
import Theorems.Thm_ThreeSum_Switch_actual_totalSize
import Theorems.Thm_ThreeSum_Switch_mem_candidates
import Theorems.Thm_ThreeSum_Switch_residual_real_identity
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
theorem _root_.solution {n j : ℕ} (hmu : 0 < mu n)
    (hj : j ≤ terminalDepth n) :
    Real.log (prefixBoxes n j : ℝ) ≤
      (mu n : ℝ) * Real.log 2 * (2 * E + 2 * bandShift - boxSaving) := by
  have hp : (prefixChoices n j : ℝ) ≠ 0 := by exact_mod_cast (prefixChoices_pos n j).ne'
  have hs : (suffixBoxes n j : ℝ) ≠ 0 := by exact_mod_cast (suffixBoxes_pos n j).ne'
  have hb := add_le_add (prefixChoices_log_bound (j := j) hmu) (suffixBoxes_log_bound hmu hj)
  have hc := (actual_switch_certified hmu hj).2.1
  have hn : (0 : ℝ) ≤ (mu n : ℝ) * Real.log 2 :=
    mul_nonneg (Nat.cast_nonneg _) log_two_pos.le
  have hmul := mul_le_mul_of_nonneg_left hc hn
  have hid := residual_real_identity hmu hj
  have hprod : (mu n : ℝ) = (blockCount (inputBits n) : ℝ) * muZero n := by
    exact_mod_cast actual_totalSize n
  have hpos := hmu
  rw [actual_totalSize] at hpos
  have hJ : (blockCount (inputBits n) : ℝ) ≠ 0 :=
    by exact_mod_cast (Nat.pos_of_mul_pos_right hpos).ne'
  have hjid : (j : ℝ) * muZero n =
      ((j : ℝ) / blockCount (inputBits n)) * mu n := by rw [hprod]; field_simp
  have hcombine : (j : ℝ) * muZero n * Real.log 2 * (2 * E + 1) +
      (residualSize n j : ℝ) * Real.log 2 *
        (2 * E - gamma ((actualSwitch n j : ℝ) / residualSize n j)) =
      (mu n : ℝ) * Real.log 2 *
        (2 * E + (j : ℝ) / blockCount (inputBits n) -
          (1 - (j : ℝ) / blockCount (inputBits n)) *
            gamma ((actualSwitch n j : ℝ) / residualSize n j)) := by
    rw [hjid, hid]
    ring
  rw [hcombine] at hb
  simp only [prefixBoxes, Nat.cast_mul, Real.log_mul hp hs]
  linear_combination hb + hmul
end ThreeSum.CostLedger
