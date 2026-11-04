-- Prove2me | solution 1 for ThreeSum.HierarchyScales.terminalDepth_le_mu
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:17:38.103094+00:00
-- url     : https://prove2.me/submissions/d0aa430d-bf10-45ca-80ca-d65bc4571efd

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Theorems.Thm_ThreeSum_Switch_actual_depth_condition
import Theorems.Thm_ThreeSum_Switch_actual_totalSize


set_option autoImplicit false
open ThreeSum ThreeSum.HierarchyScales
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch ThreeSum.CostLedger
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.HierarchyScales
theorem _root_.solution {n : ℕ} (hmu : 0 < mu n) : terminalDepth n ≤ mu n := by
  have hprod := hmu
  rw [actual_totalSize] at hprod
  have hm := Nat.pos_of_mul_pos_left hprod
  have hc := Nat.mul_le_mul_left (blockCount (inputBits n)) (show 1 ≤ muZero n by omega)
  have hd := actual_depth_condition (n := n) (j := terminalDepth n) le_rfl
  rw [Nat.mul_one, ← actual_totalSize] at hc
  omega
end ThreeSum.HierarchyScales
