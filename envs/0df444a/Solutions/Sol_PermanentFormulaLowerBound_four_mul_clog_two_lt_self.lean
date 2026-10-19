-- Prove2me | solution 1 for PermanentFormulaLowerBound.four_mul_clog_two_lt_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/1613f3e0-1985-4390-94a0-c8092c229eba

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_four_mul_le_two_pow_pred
import Theorems.Thm_PermanentFormulaLowerBound_five_le_clog_two

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution {n : ℕ} (hn : 32 ≤ n) :
    4 * Nat.clog 2 n < n := by
  have hfive := five_le_clog_two hn
  by_cases hfive_eq : Nat.clog 2 n = 5
  · omega
  · have hsix : 6 ≤ Nat.clog 2 n := by omega
    have hpow : 2 ^ (Nat.clog 2 n - 1) < n := by
      simpa using
        (Nat.pow_pred_clog_lt_self (b := 2) (by norm_num)
          (x := n) (by omega))
    exact (four_mul_le_two_pow_pred (Nat.clog 2 n) hsix).trans_lt hpow
end PermanentFormulaLowerBound
