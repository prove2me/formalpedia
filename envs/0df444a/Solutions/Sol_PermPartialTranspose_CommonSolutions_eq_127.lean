-- Prove2me | solution 1 for PermPartialTranspose.CommonSolutions.eq_127
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T20:49:44.477979+00:00
-- url     : https://prove2.me/submissions/319444b5-9758-4f7c-b51d-3fdc89a018bf

import Mathlib
import Definitions.Def_PermPartialTranspose_CommonSolutions_Ops

open PermPartialTranspose.CommonSolutions

theorem solution (d : ℕ) (hd : 3 ≤ d) (a b u v : ℂ)
    (h : onFirst (Rcheck d a u b) * onLast (Rcheck d a (u + v) b) *
          onFirst (Rcheck d a v b) =
        onLast (Rcheck d a v b) * onFirst (Rcheck d a (u + v) b) *
          onLast (Rcheck d a u b)) :
    a * b * u = a * b * (u + v) + b ^ 2 * v ∧
    a * b * v = a * b * (u + v) + b ^ 2 * u ∧
    a ^ 2 * b = a * b * (u + v) + b ^ 2 * (u + v) + b ^ 3 +
      2 * a ^ 2 * b + a * b ^ 2 * (d : ℂ) := by
  let i0 : Fin d := ⟨0, by omega⟩
  let i1 : Fin d := ⟨1, by omega⟩
  let i2 : Fin d := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  clear_value i0 i1 i2
  have e1 := congrFun (congrFun h (i0, i1, i0)) (i1, i2, i2)
  have e2 := congrFun (congrFun h (i0, i1, i1)) (i1, i0, i1)
  have e3 := congrFun (congrFun h (i0, i1, i1)) (i0, i2, i2)
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, onFirst, onLast, Rcheck, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, swapOp, pStar, partialTranspose2, smul_eq_mul,
    Prod.mk.injEq] at e1 e2 e3
  simp [ite_and, mul_add, add_mul, Finset.sum_add_distrib, h01, h02, h12,
    h01.symm, h02.symm, h12.symm] at e1 e2 e3
  refine ⟨?_, ?_, ?_⟩
  · linear_combination e1
  · linear_combination e2
  · linear_combination e3
