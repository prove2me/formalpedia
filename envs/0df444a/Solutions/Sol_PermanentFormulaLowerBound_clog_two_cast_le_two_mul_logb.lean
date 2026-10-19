-- Prove2me | solution 1 for PermanentFormulaLowerBound.clog_two_cast_le_two_mul_logb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/6b295f72-86dc-4861-bdc0-95fb2e934819

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) :
    (Nat.clog 2 n : ℝ) ≤ 2 * Real.logb 2 (n : ℝ) := by
  have hclog : 0 < Nat.clog 2 n :=
    Nat.clog_pos (by norm_num) (by omega)
  have hpow : 2 ^ (Nat.clog 2 n).pred < n :=
    Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have hpow_real :
      (2 : ℝ) ^ (Nat.clog 2 n).pred < (n : ℝ) := by
    exact_mod_cast hpow
  have hpred_log :
      ((Nat.clog 2 n).pred : ℝ) < Real.logb 2 (n : ℝ) := by
    calc
      ((Nat.clog 2 n).pred : ℝ) =
          Real.logb 2 ((2 : ℝ) ^ (Nat.clog 2 n).pred) := by
            rw [Real.logb_pow]
            norm_num
      _ < Real.logb 2 (n : ℝ) :=
        Real.logb_lt_logb (by norm_num) (by positivity) hpow_real
  have hlog_one : 1 ≤ Real.logb 2 (n : ℝ) := by
    calc
      (1 : ℝ) = Real.logb 2 (2 : ℝ) := by norm_num
      _ ≤ Real.logb 2 (n : ℝ) :=
        Real.logb_le_logb_of_le (by norm_num) (by norm_num)
          (by exact_mod_cast hn)
  have hpred :
      (Nat.clog 2 n : ℝ) = ((Nat.clog 2 n).pred : ℝ) + 1 := by
    have hpred_nat :
        Nat.clog 2 n = (Nat.clog 2 n).pred + 1 := by
      simpa [Nat.succ_eq_add_one] using
        (Nat.succ_pred_eq_of_pos hclog).symm
    exact_mod_cast hpred_nat
  linarith
end PermanentFormulaLowerBound
