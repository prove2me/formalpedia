-- Prove2me | solution 1 for ThreeSum.CostLedger.suffixBoxes_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:04:46.247779+00:00
-- url     : https://prove2.me/submissions/b0deaf0c-7a27-4ddd-9b71-3d2aff31d328

import Definitions.Def_Submission_ThreeSum_Switch
import Mathlib.Tactic.LinearCombination
import Definitions.Def_Submission_ThreeSum_CostLedger
import Theorems.Thm_ThreeSum_BinomialEntropy_log_choose_entropy_bounds
import Theorems.Thm_ThreeSum_Switch_actual_depth_condition
import Theorems.Thm_ThreeSum_Switch_actual_residual_even
import Theorems.Thm_ThreeSum_Switch_actual_residual_pos
import Theorems.Thm_ThreeSum_Switch_actual_totalSize
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
    Real.log (suffixBoxes n j : ℝ) ≤
      (residualSize n j : ℝ) * Real.log 2 *
        (2 * E - gamma ((actualSwitch n j : ℝ) / residualSize n j)) := by
  have hr := actual_residual_pos hmu hj
  have hrR : (0 : ℝ) < residualSize n j := by exact_mod_cast hr
  have hprod := hmu
  rw [actual_totalSize] at hprod
  have hspec := switchIndex_spec (Nat.pos_of_mul_pos_right hprod)
    (actual_depth_condition hj) hr (actual_residual_even n j)
  have hq : actualSwitch n j ≤ residualSize n j := by
    unfold actualSwitch
    exact hspec.1.trans (Nat.div_le_self _ _)
  have hb := (BinomialEntropy.log_choose_entropy_bounds
    (show residualSize n j - actualSwitch n j ≤ 256 * residualSize n j by omega)).2
  have hratio : ((residualSize n j - actualSwitch n j : ℕ) : ℝ) /
      ((256 * residualSize n j : ℕ) : ℝ) =
        (1 - (actualSwitch n j : ℝ) / residualSize n j) / 256 := by
    rw [Nat.cast_sub hq, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
    <;> ring
  rw [hratio, Nat.cast_mul, Nat.cast_ofNat] at hb
  have hid : (residualSize n j : ℝ) * Real.log 2 *
      (2 * E - gamma ((actualSwitch n j : ℝ) / residualSize n j)) =
        256 * (residualSize n j : ℝ) *
          Real.binEntropy ((1 - (actualSwitch n j : ℝ) / residualSize n j) / 256) := by
    unfold E gamma entropy
    field_simp
    <;> ring
  rw [hid]
  exact hb
end ThreeSum.CostLedger
