-- Prove2me | solution 1 for PermPartialTranspose.CommonSolutions.tl_identities
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T20:10:10.93109+00:00
-- url     : https://prove2.me/submissions/75a043bd-a7c2-4168-bab8-610f0d82bf27

import Mathlib
import Definitions.Def_PermPartialTranspose_CommonSolutions_Ops

open PermPartialTranspose.CommonSolutions

theorem solution (d : ℕ) :
    swapOp d * pStar d = pStar d ∧
    pStar d * swapOp d = pStar d ∧
    pStar d * pStar d = (d : ℂ) • pStar d := by
  refine ⟨?_, ?_, ?_⟩
  · ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.mul_apply, swapOp, pStar, partialTranspose2, Fintype.sum_prod_type]
    simp [ite_and, eq_comm]
    split_ifs <;> rfl
  · ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.mul_apply, swapOp, pStar, partialTranspose2, Fintype.sum_prod_type]
    simp [ite_and, eq_comm]
  · ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.mul_apply, swapOp, pStar, partialTranspose2, Fintype.sum_prod_type,
      Matrix.smul_apply]
    simp [ite_and, eq_comm]
    split_ifs <;> rfl
