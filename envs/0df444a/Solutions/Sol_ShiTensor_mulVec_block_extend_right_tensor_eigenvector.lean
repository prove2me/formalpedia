-- Prove2me | solution 1 for ShiTensor.mulVec_block_extend_right_tensor_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-16T01:29:15.396186+00:00
-- url     : https://prove2.me/submissions/13d15777-5471-4b11-913a-0e96b873f99d

import Definitions.Def_ShiTensor_Core
import Definitions.Def_ShiShallow_Matrix
import Theorems.Thm_ShiTensor_sum_split_factor

set_option autoImplicit false

open ShiShallow ShiTensor

/-- Reshuffle one summand so the left-block guard sits on the LEFT factor and the operator entry
sits on the RIGHT factor, ready for `ShiTensor.sum_split_factor`. -/
private lemma shiBr_term {m p : ℕ} (A : Op p) (u : Bits m → ℂ) (v : Bits p → ℂ)
    (y z : Bits (m + p)) :
    (if leftBits y = leftBits z then A (rightBits y) (rightBits z) else 0)
        * (u (leftBits z) * v (rightBits z))
      = (if leftBits y = leftBits z then u (leftBits z) else 0)
        * (A (rightBits y) (rightBits z) * v (rightBits z)) := by
  by_cases h : leftBits y = leftBits z
  · first
      | (simp only [if_pos h]; ring; done)
      | (rw [if_pos h, if_pos h]; ring; done)
      | (rw [if_pos h]; ring; done)
  · first
      | (simp only [if_neg h]; ring; done)
      | (rw [if_neg h, if_neg h]; ring; done)
      | (rw [if_neg h]; ring; done)

theorem solution {m p : ℕ} (A : Op p) (α : ℂ)
    (u : Bits m → ℂ) (v : Bits p → ℂ)
    (hv : ∀ b' : Bits p, ∑ b : Bits p, A b' b * v b = α * v b') :
    Matrix.mulVec
        (Matrix.of fun y z : Bits (m + p) =>
          if leftBits y = leftBits z then A (rightBits y) (rightBits z) else 0)
        (fun y => u (leftBits y) * v (rightBits y))
      = fun y => α * (u (leftBits y) * v (rightBits y)) := by
  funext y
  show Matrix.mulVec _ _ y = α * (u (leftBits y) * v (rightBits y))
  have hmv : Matrix.mulVec
        (Matrix.of fun y' z' : Bits (m + p) =>
          if leftBits y' = leftBits z' then A (rightBits y') (rightBits z') else 0)
        (fun w => u (leftBits w) * v (rightBits w)) y
      = ∑ z : Bits (m + p),
          (if leftBits y = leftBits z then A (rightBits y) (rightBits z) else 0)
            * (u (leftBits z) * v (rightBits z)) := by
    first
      | rfl
      | (simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]; done)
      | (simp [Matrix.mulVec, dotProduct]; done)
  have hsplit : (∑ z : Bits (m + p),
        (if leftBits y = leftBits z then u (leftBits z) else 0)
          * (A (rightBits y) (rightBits z) * v (rightBits z)))
      = (∑ a : Bits m, if leftBits y = a then u a else 0)
        * ∑ b : Bits p, A (rightBits y) b * v b := by
    first
      | exact sum_split_factor (fun a : Bits m => if leftBits y = a then u a else 0)
          (fun b : Bits p => A (rightBits y) b * v b)
      | exact ShiTensor.sum_split_factor (R := ℂ)
          (fun a : Bits m => if leftBits y = a then u a else 0)
          (fun b : Bits p => A (rightBits y) b * v b)
  have hleft : (∑ a : Bits m, if leftBits y = a then u a else 0) = u (leftBits y) := by
    first
      | (rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ (leftBits y))]; done)
      | (simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]; done)
      | (simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]; done)
      | (simp; done)
  rw [hmv]
  calc ∑ z : Bits (m + p),
        (if leftBits y = leftBits z then A (rightBits y) (rightBits z) else 0)
          * (u (leftBits z) * v (rightBits z))
      = ∑ z : Bits (m + p),
          (if leftBits y = leftBits z then u (leftBits z) else 0)
            * (A (rightBits y) (rightBits z) * v (rightBits z)) :=
        Finset.sum_congr rfl (fun z _ => shiBr_term A u v y z)
    _ = (∑ a : Bits m, if leftBits y = a then u a else 0)
          * ∑ b : Bits p, A (rightBits y) b * v b := hsplit
    _ = u (leftBits y) * (α * v (rightBits y)) := by
        rw [hleft, hv (rightBits y)]
    _ = α * (u (leftBits y) * v (rightBits y)) := by ring
