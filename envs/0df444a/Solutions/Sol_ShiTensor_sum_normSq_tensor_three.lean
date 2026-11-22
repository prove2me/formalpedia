-- Prove2me | solution 1 for ShiTensor.sum_normSq_tensor_three
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-14T07:28:20.166314+00:00
-- url     : https://prove2.me/submissions/53897175-c488-4b77-860d-e3465d0dd9ff

import Definitions.Def_ShiTensor_Core

set_option autoImplicit false

section
open ShiShallow ShiTensor

private theorem shiNrm_leftBits_append {m p : ℕ} (a : Bits m) (b : Bits p) :
    leftBits (Fin.append a b) = a := by
  funext i; simp [leftBits, Fin.append_left]

private theorem shiNrm_rightBits_append {m p : ℕ} (a : Bits m) (b : Bits p) :
    rightBits (Fin.append a b) = b := by
  funext j; simp [rightBits, Fin.append_right]

private theorem shiNrm_append_leftBits_rightBits {m p : ℕ} (y : Bits (m + p)) :
    Fin.append (leftBits y) (rightBits y) = y := by
  -- `simpa` unfolds the USING term but leaves the goal folded, so they fail to match.
  -- `exact` checks at DEFAULT transparency, where `leftBits y` IS `y ∘ Fin.castAdd p`.
  exact Fin.append_castAdd_natAdd

private def shiNrm_equiv (m p : ℕ) : Bits (m + p) ≃ Bits m × Bits p where
  toFun y := (leftBits y, rightBits y)
  invFun q := Fin.append q.1 q.2
  left_inv y := shiNrm_append_leftBits_rightBits y
  right_inv q := by
    obtain ⟨a, b⟩ := q
    simp [shiNrm_leftBits_append a b, shiNrm_rightBits_append a b]

private theorem shiNrm_sum_factor {m p : ℕ} {R : Type*} [NonUnitalNonAssocSemiring R]
    (f : Bits m → R) (g : Bits p → R) :
    ∑ y : Bits (m + p), f (leftBits y) * g (rightBits y)
      = (∑ a : Bits m, f a) * ∑ b : Bits p, g b := by
  calc
    ∑ y : Bits (m + p), f (leftBits y) * g (rightBits y)
        = ∑ q : Bits m × Bits p, f q.1 * g q.2 :=
          Fintype.sum_equiv (shiNrm_equiv m p) (fun y => f (leftBits y) * g (rightBits y))
            (fun q => f q.1 * g q.2) (fun y => rfl)
    _ = ∑ a : Bits m, ∑ b : Bits p, f a * g b :=
          Fintype.sum_prod_type' (f := fun a b => f a * g b)
    _ = (∑ a : Bits m, f a) * ∑ b : Bits p, g b := (Fintype.sum_mul_sum f g).symm

private theorem shiNrm_sum_normSq_tensor {m p : ℕ} (ψ : QState m) (φ : QState p) :
    ∑ y : Bits (m + p), ‖tensor ψ φ y‖ ^ 2
      = (∑ a : Bits m, ‖ψ a‖ ^ 2) * ∑ b : Bits p, ‖φ b‖ ^ 2 := by
  have hpt : ∀ y : Bits (m + p),
      ‖tensor ψ φ y‖ ^ 2 = ‖ψ (leftBits y)‖ ^ 2 * ‖φ (rightBits y)‖ ^ 2 := by
    intro y
    show ‖ψ (leftBits y) * φ (rightBits y)‖ ^ 2
        = ‖ψ (leftBits y)‖ ^ 2 * ‖φ (rightBits y)‖ ^ 2
    rw [norm_mul, mul_pow]
  simp only [hpt]
  exact shiNrm_sum_factor (R := ℝ) (fun a => ‖ψ a‖ ^ 2) (fun b => ‖φ b‖ ^ 2)

/-- A threefold amplitude-array tensor product of normalised states is normalised.

`Bits (m + p + q)` parses as `Bits ((m + p) + q)`, which is exactly the type of
`tensor (tensor ψ φ) χ`, so no associativity transport is involved. -/
theorem solution {m p q : ℕ} (ψ : QState m) (φ : QState p) (χ : QState q)
    (hψ : ∑ a : Bits m, ‖ψ a‖ ^ 2 = 1)
    (hφ : ∑ b : Bits p, ‖φ b‖ ^ 2 = 1)
    (hχ : ∑ c : Bits q, ‖χ c‖ ^ 2 = 1) :
    ∑ y : Bits (m + p + q), ‖tensor (tensor ψ φ) χ y‖ ^ 2 = 1 := by
  rw [shiNrm_sum_normSq_tensor (tensor ψ φ) χ, shiNrm_sum_normSq_tensor ψ φ, hψ, hφ, hχ]
  first
    | done
    | (norm_num; done)
    | (simp; done)

end
