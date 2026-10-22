-- Prove2me | solution 1 for PermPartialTranspose.CommonSolutions.eq_66_67
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T20:17:06.220769+00:00
-- url     : https://prove2.me/submissions/88623cef-cb84-422e-b8ae-532b935c2d38

import Mathlib
import Definitions.Def_PermPartialTranspose_CommonSolutions_Ops

open PermPartialTranspose.CommonSolutions

set_option maxHeartbeats 8000000 in
theorem solution :
    BraidRel (swapOp 2) ∧
    BraidRel (pBar 2) ∧
    swapOp 2 * swapOp 2 = 1 ∧
    pBar 2 * pBar 2 = 1 ∧
    onFirst (swapOp 2) * onLast (pBar 2) * onFirst (swapOp 2) =
      onLast (swapOp 2) * onFirst (pBar 2) * onLast (swapOp 2) ∧
    onFirst (swapOp 2) * onLast (pBar 2) * onFirst (pBar 2) =
      onLast (pBar 2) * onFirst (pBar 2) * onLast (swapOp 2) ∧
    onFirst (pBar 2) * onLast (pBar 2) * onFirst (swapOp 2) =
      onLast (swapOp 2) * onFirst (pBar 2) * onLast (pBar 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold BraidRel; (
    ext ⟨i, j, k⟩ ⟨i', j', k'⟩
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, onFirst, onLast, pBar,
      Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, swapOp, pStar,
      partialTranspose2, smul_eq_mul, Prod.mk.injEq]
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases i' <;> fin_cases j' <;> fin_cases k' <;>
      simp <;> ring)
  · unfold BraidRel; (
    ext ⟨i, j, k⟩ ⟨i', j', k'⟩
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, onFirst, onLast, pBar,
      Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, swapOp, pStar,
      partialTranspose2, smul_eq_mul, Prod.mk.injEq]
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases i' <;> fin_cases j' <;> fin_cases k' <;>
      simp <;> ring)
  · (
    ext ⟨i, j⟩ ⟨i', j'⟩
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, pBar,
      Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, swapOp, pStar,
      partialTranspose2, smul_eq_mul, Prod.mk.injEq]
    fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;> simp)
  · (
    ext ⟨i, j⟩ ⟨i', j'⟩
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, pBar,
      Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, swapOp, pStar,
      partialTranspose2, smul_eq_mul, Prod.mk.injEq]
    fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;> simp)
  · (
    ext ⟨i, j, k⟩ ⟨i', j', k'⟩
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, onFirst, onLast, pBar,
      Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, swapOp, pStar,
      partialTranspose2, smul_eq_mul, Prod.mk.injEq]
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases i' <;> fin_cases j' <;> fin_cases k' <;>
      simp <;> ring)
  · (
    ext ⟨i, j, k⟩ ⟨i', j', k'⟩
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, onFirst, onLast, pBar,
      Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, swapOp, pStar,
      partialTranspose2, smul_eq_mul, Prod.mk.injEq]
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases i' <;> fin_cases j' <;> fin_cases k' <;>
      simp <;> ring)
  · (
    ext ⟨i, j, k⟩ ⟨i', j', k'⟩
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, onFirst, onLast, pBar,
      Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, swapOp, pStar,
      partialTranspose2, smul_eq_mul, Prod.mk.injEq]
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases i' <;> fin_cases j' <;> fin_cases k' <;>
      simp <;> ring)
