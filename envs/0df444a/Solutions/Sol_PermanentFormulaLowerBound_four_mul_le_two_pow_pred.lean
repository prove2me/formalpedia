-- Prove2me | solution 1 for PermanentFormulaLowerBound.four_mul_le_two_pow_pred
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/8a64d79a-e650-4f4e-b5ac-127fd470da39

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution (ell : ℕ) (hell : 6 ≤ ell) :
    4 * ell ≤ 2 ^ (ell - 1) := by
  induction ell, hell using Nat.le_induction with
  | base => norm_num
  | succ ell hell ih =>
      have hell_pos : 1 ≤ ell := by omega
      calc
        4 * (ell + 1) ≤ 2 * (4 * ell) := by omega
        _ ≤ 2 * 2 ^ (ell - 1) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ ((ell + 1) - 1) := by
          calc
            2 * 2 ^ (ell - 1) = 2 ^ (ell - 1) * 2 := by ac_rfl
            _ = 2 ^ (ell - 1 + 1) := by rw [pow_succ]
            _ = 2 ^ ((ell + 1) - 1) := by
              congr 1
              omega
end PermanentFormulaLowerBound
