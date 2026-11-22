-- Prove2me | solution 1 for ShiTensor.tensor_split_append_inverse
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-13T05:06:43.531826+00:00
-- url     : https://prove2.me/submissions/c7bc3038-9e9e-4782-9f96-cd64b090c8e6

import Definitions.Def_ShiTensor_Core

set_option autoImplicit false

section
open ShiShallow ShiTensor

private theorem shiTen_leftBits_append {m p : ℕ} (a : Bits m) (b : Bits p) :
    leftBits (Fin.append a b) = a := by
  funext i; simp [leftBits, Fin.append_left]

private theorem shiTen_rightBits_append {m p : ℕ} (a : Bits m) (b : Bits p) :
    rightBits (Fin.append a b) = b := by
  funext j; simp [rightBits, Fin.append_right]

private theorem shiTen_append_leftBits_rightBits {m p : ℕ} (y : Bits (m + p)) :
    Fin.append (leftBits y) (rightBits y) = y := by
  -- `simpa` unfolds the USING term but leaves the goal folded, so they fail to match.
  -- `exact` checks at DEFAULT transparency, where `leftBits y` IS `y ∘ Fin.castAdd p`.
  exact Fin.append_castAdd_natAdd

private def shiTen_equiv (m p : ℕ) : Bits (m + p) ≃ Bits m × Bits p where
  toFun y := (leftBits y, rightBits y)
  invFun q := Fin.append q.1 q.2
  left_inv y := shiTen_append_leftBits_rightBits y
  right_inv q := by
    obtain ⟨a, b⟩ := q
    simp [shiTen_leftBits_append a b, shiTen_rightBits_append a b]

theorem solution {m p : ℕ} :
    (∀ (a : Bits m) (b : Bits p), leftBits (Fin.append a b) = a) ∧
    (∀ (a : Bits m) (b : Bits p), rightBits (Fin.append a b) = b) ∧
    (∀ (y : Bits (m + p)), Fin.append (leftBits y) (rightBits y) = y) :=
  ⟨shiTen_leftBits_append, shiTen_rightBits_append, shiTen_append_leftBits_rightBits⟩

end
