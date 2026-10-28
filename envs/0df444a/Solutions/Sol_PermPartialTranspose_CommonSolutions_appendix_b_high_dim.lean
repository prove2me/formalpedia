-- Prove2me | solution 1 for PermPartialTranspose.CommonSolutions.appendix_b_high_dim
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T20:50:59.466127+00:00
-- url     : https://prove2.me/submissions/902860a7-11c1-407e-8571-bf1cc450ee0c

import Mathlib
import Definitions.Def_PermPartialTranspose_CommonSolutions_Ops

open PermPartialTranspose.CommonSolutions

theorem e127X (d : ℕ) (hd : 3 ≤ d) (a b u v : ℂ)
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

theorem entryX (d : ℕ) (hd : 3 ≤ d) (a b x y z : ℂ)
    (h : onFirst (Rcheck d a x b) * onLast (Rcheck d a y b) * onFirst (Rcheck d a z b) =
        onLast (Rcheck d a z b) * onFirst (Rcheck d a y b) * onLast (Rcheck d a x b)) :
    a ^ 2 * (x - y + z) = 0 := by
  let i0 : Fin d := ⟨0, by omega⟩
  let i1 : Fin d := ⟨1, by omega⟩
  let i2 : Fin d := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  clear_value i0 i1 i2
  have e := congrFun (congrFun h (i0, i1, i2)) (i1, i0, i2)
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, onFirst, onLast, Rcheck, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, swapOp, pStar, partialTranspose2, smul_eq_mul,
    Prod.mk.injEq] at e
  simp [ite_and, mul_add, add_mul, Finset.sum_add_distrib, h01, h02, h12,
    h01.symm, h02.symm, h12.symm] at e
  linear_combination e

theorem solution (d : ℕ) (hd : 3 ≤ d) (a b : ℂ) (ha : a ≠ 0) :
    (∀ u : ℂ, u ≠ 0 → ¬ BraidRel (Rcheck d a u b)) ∧
    ¬ MultiplicativeYBE d a b ∧
    (b ≠ 0 → ¬ AdditiveYBE d a b) := by
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  refine ⟨?_, ?_, ?_⟩
  · intro u hu hB
    have := entryX d hd a b u u u hB
    rcases mul_eq_zero.mp this with h | h
    · exact ha2 h
    · exact hu (by linear_combination h)
  · intro hM
    have := entryX d hd a b 1 (1 * 1) 1 (hM 1 1)
    rcases mul_eq_zero.mp this with h | h
    · exact ha2 h
    · norm_num at h
  · intro hb hA
    obtain ⟨h1, -, h3⟩ := e127X d hd a b 0 1 (hA 0 1)
    have hab : a = -b := by
      have : b * (a + b) = 0 := by linear_combination -h1
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hb
      · linear_combination h
    subst hab
    have h4 : b ^ 3 * (2 - (d : ℂ)) = 0 := by linear_combination -h3
    rcases mul_eq_zero.mp h4 with h | h
    · exact hb (pow_eq_zero_iff (by norm_num) |>.mp h)
    · have : (d : ℂ) = 2 := by linear_combination -h
      have : d = 2 := by exact_mod_cast this
      omega
