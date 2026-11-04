-- Prove2me | solution 1 for ThreeSum.CostLedger.queryTerms_log_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:29:20.550755+00:00
-- url     : https://prove2.me/submissions/b50bd745-b56b-43fc-9c8a-47ad246b4bfb

import Definitions.Def_Submission_ThreeSum_Switch
import Mathlib.Tactic.LinearCombination
import Definitions.Def_Submission_ThreeSum_CostLedger
import Theorems.Thm_ThreeSum_BinomialEntropy_log_choose_entropy_bounds
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_ThreeSum_Switch_actual_depth_condition
import Theorems.Thm_ThreeSum_Switch_actual_residual_even
import Theorems.Thm_ThreeSum_Switch_actual_residual_pos
import Definitions.Def_WeightedCache3SUM_Alias_99dfc3473a1cfe41
import Theorems.Thm_ThreeSum_Switch_actual_totalSize
import Theorems.Thm_ThreeSum_Switch_residual_real_identity
import Theorems.Thm_ThreeSum_Switch_switchIndex_spec


set_option autoImplicit false
open ThreeSum ThreeSum.CostLedger
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch
open scoped Topology BigOperators
set_option maxHeartbeats 400000
noncomputable section
namespace ThreeSum.CostLedger
theorem _root_.solution {n j : ℕ} (hmu : 0 < mu n)
    (hj : j ≤ terminalDepth n) :
    Real.log (queryTerms n j : ℝ) ≤
      (mu n : ℝ) * Real.log 2 * (entropyRatio * (1 + boxSaving - 2 * bandShift)) +
        9 * entropyRatio * Real.log 2 := by
  have hprod := hmu
  rw [actual_totalSize] at hprod
  have hr := actual_residual_pos hmu hj
  have hq := (switchIndex_spec (Nat.pos_of_mul_pos_right hprod)
    (actual_depth_condition hj) hr (actual_residual_even n j)).1
  have hb := (BinomialEntropy.log_choose_entropy_bounds
    (hq.trans (Nat.div_le_self _ _))).2
  have hc := (actual_switch_certified hmu hj).2.2
  have hmuR : (0 : ℝ) < mu n := by exact_mod_cast hmu
  have hmul := mul_lt_mul_of_pos_left hc (mul_pos hmuR log_two_pos)
  have hid : (residualSize n j : ℝ) *
      Real.binEntropy ((actualSwitch n j : ℝ) / residualSize n j) =
      (mu n : ℝ) * Real.log 2 *
        ((1 - (j : ℝ) / blockCount (inputBits n)) *
          entropy ((actualSwitch n j : ℝ) / residualSize n j)) := by
    rw [residual_real_identity hmu hj]
    unfold entropy
    field_simp
    <;> ring
  change Real.log (queryTerms n j : ℝ) ≤
    (residualSize n j : ℝ) * Real.binEntropy ((actualSwitch n j : ℝ) / residualSize n j) at hb
  rw [hid] at hb
  have hround : (mu n : ℝ) * Real.log 2 *
      (entropyRatio * (1 + boxSaving - 2 * bandShift) + 9 * entropyRatio / mu n) =
      (mu n : ℝ) * Real.log 2 * (entropyRatio * (1 + boxSaving - 2 * bandShift)) +
        9 * entropyRatio * Real.log 2 := by field_simp
  rw [hround] at hmul
  exact hb.trans hmul.le
end ThreeSum.CostLedger
