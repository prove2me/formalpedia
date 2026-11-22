-- Prove2me | solution 1 for ShiTensor.sum_split_factor
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-13T05:06:42.182336+00:00
-- url     : https://prove2.me/submissions/2b8d15fe-ab7b-41c3-aeb5-bd775e0c6d32

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
  -- `simpa` unfolds the USING term but leaves the goal folded; `exact` checks at
  -- DEFAULT transparency, where `leftBits y` IS `y ∘ Fin.castAdd p`.
  exact Fin.append_castAdd_natAdd

private def shiTen_equiv (m p : ℕ) : Bits (m + p) ≃ Bits m × Bits p where
  toFun y := (leftBits y, rightBits y)
  invFun q := Fin.append q.1 q.2
  left_inv y := shiTen_append_leftBits_rightBits y
  right_inv q := by
    obtain ⟨a, b⟩ := q
    simp [shiTen_leftBits_append a b, shiTen_rightBits_append a b]

private theorem shiTen_sum_factor {m p : ℕ} {R : Type*} [NonUnitalNonAssocSemiring R]
    (f : Bits m → R) (g : Bits p → R) :
    ∑ y : Bits (m + p), f (leftBits y) * g (rightBits y)
      = (∑ a : Bits m, f a) * ∑ b : Bits p, g b := by
  calc
    ∑ y : Bits (m + p), f (leftBits y) * g (rightBits y)
        = ∑ q : Bits m × Bits p, f q.1 * g q.2 :=
          Fintype.sum_equiv (shiTen_equiv m p) (fun y => f (leftBits y) * g (rightBits y))
            (fun q => f q.1 * g q.2) (fun y => rfl)
    _ = ∑ a : Bits m, ∑ b : Bits p, f a * g b :=
          Fintype.sum_prod_type' (f := fun a b => f a * g b)
    _ = (∑ a : Bits m, f a) * ∑ b : Bits p, g b := (Fintype.sum_mul_sum f g).symm

theorem solution {m p : ℕ} {R : Type*} [NonUnitalNonAssocSemiring R]
    (f : Bits m → R) (g : Bits p → R) :
    ∑ y : Bits (m + p), f (leftBits y) * g (rightBits y)
      = (∑ a : Bits m, f a) * ∑ b : Bits p, g b :=
  shiTen_sum_factor f g

end
