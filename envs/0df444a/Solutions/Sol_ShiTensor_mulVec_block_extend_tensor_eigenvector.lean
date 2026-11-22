-- Prove2me | solution 1 for ShiTensor.mulVec_block_extend_tensor_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-13T19:32:13.815075+00:00
-- url     : https://prove2.me/submissions/25b5c860-4bc9-44af-8958-5aaa437b28fc

import Definitions.Def_ShiTensor_Core
import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

open ShiShallow ShiTensor

private lemma shiEigm_leftBits_append {m p : ℕ} (a : Bits m) (b : Bits p) :
    leftBits (Fin.append a b) = a := by
  funext i
  simp [leftBits, Fin.append_left]

private lemma shiEigm_rightBits_append {m p : ℕ} (a : Bits m) (b : Bits p) :
    rightBits (Fin.append a b) = b := by
  funext j
  simp [rightBits, Fin.append_right]

private lemma shiEigm_sum_split {m p : ℕ} (F : Bits (m + p) → ℂ) :
    ∑ z : Bits (m + p), F z = ∑ a : Bits m, ∑ b : Bits p, F (Fin.append a b) := by
  have h1 : ∑ q : (Fin m → Bool) × (Fin p → Bool), F (Fin.append q.1 q.2)
      = ∑ z : Bits (m + p), F z :=
    Fintype.sum_equiv (Fin.appendEquiv m p) (fun q => F (Fin.append q.1 q.2)) F
      (fun q => by first | rfl | (simp [Fin.appendEquiv]; done))
  rw [← h1]
  first
    | exact Fintype.sum_prod_type _
    | (rw [Fintype.sum_prod_type]; done)
    | (simp [Fintype.sum_prod_type]; done)

theorem solution {m p : ℕ} (A : Op m) (α : ℂ)
    (u : Bits m → ℂ) (v : Bits p → ℂ)
    (hu : ∀ a' : Bits m, ∑ a : Bits m, A a' a * u a = α * u a') :
    Matrix.mulVec
        (Matrix.of fun y z : Bits (m + p) =>
          if rightBits y = rightBits z then A (leftBits y) (leftBits z) else 0)
        (fun y => u (leftBits y) * v (rightBits y))
      = fun y => α * (u (leftBits y) * v (rightBits y)) := by
  funext y
  show Matrix.mulVec _ _ y = α * (u (leftBits y) * v (rightBits y))
  have hmv : Matrix.mulVec
        (Matrix.of fun y' z' : Bits (m + p) =>
          if rightBits y' = rightBits z' then A (leftBits y') (leftBits z') else 0)
        (fun w => u (leftBits w) * v (rightBits w)) y
      = ∑ z : Bits (m + p),
          (if rightBits y = rightBits z then A (leftBits y) (leftBits z) else 0)
            * (u (leftBits z) * v (rightBits z)) := by
    first
      | rfl
      | (simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]; done)
      | (simp [Matrix.mulVec, dotProduct]; done)
  rw [hmv, shiEigm_sum_split]
  simp only [shiEigm_leftBits_append, shiEigm_rightBits_append, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [show (α * (u (leftBits y) * v (rightBits y)) : ℂ)
        = α * u (leftBits y) * v (rightBits y) from by ring,
    ← hu (leftBits y), Finset.sum_mul]
  first
    | exact Finset.sum_congr rfl fun a _ => (mul_assoc _ _ _).symm
    | (simp [mul_assoc]; done)
