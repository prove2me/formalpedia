-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.qBinom_mul_frameProd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:55:02.914819+00:00
-- url     : https://prove2.me/submissions/6d39088a-cbda-4038-97ff-2ba7ba95857d

import Definitions.Def_SharpIntermediateSubgroupBounds_Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Theorems.Thm_SharpIntermediateSubgroupBounds_qFactorial_pos
import Theorems.Thm_SharpIntermediateSubgroupBounds_qBinom_mul_qFactorials
import Theorems.Thm_SharpIntermediateSubgroupBounds_frameProd_mul_qFactorial

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {q n k : ℕ} (hq : 2 ≤ q) (hk : k ≤ n) :
    qBinom q n k * frameProd q k k = frameProd q n k := by
  have hmain := frameProd_mul_qFactorial (q := q) (n := n) hk
  have hdiag := frameProd_mul_qFactorial (q := q) (n := k) (le_refl k)
  have hqbin := qBinom_mul_qFactorials hq hk
  simp only [Nat.sub_self, qFactorial_zero, mul_one] at hdiag
  have hcancel : 0 < qFactorial q (n - k) := qFactorial_pos hq _
  apply Nat.eq_of_mul_eq_mul_right hcancel
  calc
    qBinom q n k * frameProd q k k * qFactorial q (n - k) =
        framePower q k *
          (qBinom q n k * qFactorial q k * qFactorial q (n - k)) := by
            rw [hdiag]
            ring
    _ = framePower q k * qFactorial q n := by rw [hqbin]
    _ = frameProd q n k * qFactorial q (n - k) := hmain.symm
end SharpIntermediateSubgroupBounds
