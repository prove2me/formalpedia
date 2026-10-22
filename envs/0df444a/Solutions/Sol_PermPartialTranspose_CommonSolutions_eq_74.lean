-- Prove2me | solution 1 for PermPartialTranspose.CommonSolutions.eq_74
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T20:14:19.300026+00:00
-- url     : https://prove2.me/submissions/88e834fc-6c45-4800-b74d-a8a991ed7f0a

import Mathlib
import Definitions.Def_PermPartialTranspose_CommonSolutions_Ops

open PermPartialTranspose.CommonSolutions

set_option maxHeartbeats 8000000 in
theorem solution (a x y z : ℂ) :
    onFirst (a • pBar 2 + x • swapOp 2) *
        onLast (a • pBar 2 + z • swapOp 2) *
        onFirst (a • pBar 2 + y • swapOp 2) =
      onLast (a • pBar 2 + y • swapOp 2) *
        onFirst (a • pBar 2 + z • swapOp 2) *
        onLast (a • pBar 2 + x • swapOp 2) := by
  ext ⟨i, j, k⟩ ⟨i', j', k'⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, onFirst, onLast, pBar,
    Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, swapOp, pStar,
    partialTranspose2, smul_eq_mul, Prod.mk.injEq]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases i' <;> fin_cases j' <;> fin_cases k' <;>
    simp <;> ring
