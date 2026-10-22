-- Prove2me | solution 1 for PermPartialTranspose.CommonSolutions.eq_70
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T20:11:33.848989+00:00
-- url     : https://prove2.me/submissions/17866386-1eaa-4c86-89b9-1b6ddd11a8d5

import Mathlib
import Definitions.Def_PermPartialTranspose_CommonSolutions_Ops

open PermPartialTranspose.CommonSolutions

set_option maxHeartbeats 4000000 in
theorem solution (a : ℂ) (ha : a ≠ 0) : BraidRel (Rcheck 2 a (-a) a) := by
  unfold BraidRel
  ext ⟨i, j, k⟩ ⟨i', j', k'⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, onFirst, onLast, Rcheck,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, swapOp, pStar, partialTranspose2,
    smul_eq_mul, Prod.mk.injEq]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases i' <;> fin_cases j' <;> fin_cases k' <;>
    simp <;> ring
