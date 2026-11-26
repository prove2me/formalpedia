-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.qBinom_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:43:04.899028+00:00
-- url     : https://prove2.me/submissions/cb03c0e2-05d0-4d60-aa06-d00765c8205b

import Definitions.Def_SharpIntermediateSubgroupBounds_Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Theorems.Thm_SharpIntermediateSubgroupBounds_qFactorial_pos
import Theorems.Thm_SharpIntermediateSubgroupBounds_qBinom_mul_qFactorials

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {q n k : ℕ} (hq : 2 ≤ q) (hk : k ≤ n) :
    qBinom q n k = qBinom q n (n - k) := by
  have hleft := qBinom_mul_qFactorials hq hk
  have hright := qBinom_mul_qFactorials hq (Nat.sub_le n k)
  rw [tsub_tsub_cancel_of_le hk] at hright
  have hden : 0 < qFactorial q k * qFactorial q (n - k) :=
    Nat.mul_pos (qFactorial_pos hq k) (qFactorial_pos hq (n - k))
  apply Nat.eq_of_mul_eq_mul_right hden
  calc
    qBinom q n k * (qFactorial q k * qFactorial q (n - k)) = qFactorial q n := by
      simpa [mul_assoc] using hleft
    _ = qBinom q n (n - k) * (qFactorial q k * qFactorial q (n - k)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hright.symm
end SharpIntermediateSubgroupBounds
