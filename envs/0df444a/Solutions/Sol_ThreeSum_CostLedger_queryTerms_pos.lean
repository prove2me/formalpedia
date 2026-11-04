-- Prove2me | solution 1 for ThreeSum.CostLedger.queryTerms_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:33:47.297887+00:00
-- url     : https://prove2.me/submissions/6bf845c5-3f59-4281-b3f5-64349eb4fe1e

import Definitions.Def_Submission_ThreeSum_Switch
import Mathlib.Tactic.LinearCombination
import Definitions.Def_Submission_ThreeSum_CostLedger
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
    (hj : j ≤ terminalDepth n) : 0 < queryTerms n j := by
  have hprod := hmu
  rw [actual_totalSize] at hprod
  have hq := (switchIndex_spec (Nat.pos_of_mul_pos_right hprod)
    (actual_depth_condition hj) (actual_residual_pos hmu hj) (actual_residual_even n j)).1
  exact Nat.choose_pos (hq.trans (Nat.div_le_self _ _))
end ThreeSum.CostLedger
