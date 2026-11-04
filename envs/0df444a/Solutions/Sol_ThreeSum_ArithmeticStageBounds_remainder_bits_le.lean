-- Prove2me | solution 1 for ThreeSum.ArithmeticStageBounds.remainder_bits_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:59:04.641226+00:00
-- url     : https://prove2.me/submissions/2576e2f6-e34d-41da-b1e6-a548122fbfe4

import Definitions.Def_Submission_ThreeSum_ModuloCosts
import Definitions.Def_Submission_ThreeSum_BudgetTime
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Theorems.Thm_ThreeSum_ArithmeticStageBounds_bits_le_window_square
import Theorems.Thm_ThreeSum_Scales_log2_difference_bound


set_option autoImplicit false
open ThreeSum ThreeSum.ArithmeticStageBounds
open Filter Real Parameters Scales BandScales CostLedger HierarchyScales
  MassScales StageBounds UniformStageBounds ModuloCosts
open scoped Topology
set_option maxHeartbeats 1000000
namespace ThreeSum.ArithmeticStageBounds
theorem _root_.solution {n : ℕ} (k : ℕ) (hn : 0 < n) :
    Nat.log 2 (n^k+1)+1 ≤ bitBudget k n := by
  have hp : 0 < n^k := Nat.pow_pos hn
  have hm := Nat.log_mono_right (b := 2) (show n^k+1 ≤ 3*n^k by omega)
  have hl := log2_difference_bound k hn
  rw [Nat.log2_eq_log_two] at hl
  have hw := Nat.mul_le_mul_left (2*(k+2)) (bits_le_window_square n)
  unfold bitBudget
  omega
end ThreeSum.ArithmeticStageBounds
