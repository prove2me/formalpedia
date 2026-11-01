-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P20.splitSemidirectDecomposition
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-31T12:19:00.466682+00:00
-- url     : https://prove2.me/submissions/45390f3f-cdef-423f-8c6e-b88a3f7af6b7

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20
import Mathlib.Tactic.Group

set_option autoImplicit false
open QAlgorithms.Papers.Independent.Intake100.P20
universe u v

theorem solution {A : Type u} {O : Type v} [Group A] [Group O]
    (s : A →* O) (e : O →* A) (h : ∀ x, s (e x) = x) :
    ∃ q : A ≃* SemidirectProduct s.ker O (splitAction s e),
      (∀ a, q a = splitCoordinates s e h a) ∧
      (∀ a, q.symm a = splitAssembly s e a) ∧
      (∀ x (k : s.ker), ((splitAction s e x) k).val = e x * k.val * (e x)⁻¹) := by
  let q : A ≃* SemidirectProduct s.ker O (splitAction s e) :=
    { toFun := splitCoordinates s e h
      invFun := splitAssembly s e
      left_inv := by
        intro a
        change (a * (e (s a))⁻¹) * e (s a) = a
        group
      right_inv := by
        intro a
        apply SemidirectProduct.ext
        · apply Subtype.ext
          change (a.left.val * e a.right) * (e (s (a.left.val * e a.right)))⁻¹ = a.left.val
          have hk : s a.left.val = 1 := a.left.property
          simp only [map_mul, hk, h, one_mul, mul_inv_cancel_right]
        · change s (a.left.val * e a.right) = a.right
          have hk : s a.left.val = 1 := a.left.property
          simp only [map_mul, hk, h, one_mul]
      map_mul' := by
        intro a b
        apply SemidirectProduct.ext
        · apply Subtype.ext
          change a * b * (e (s (a * b)))⁻¹ =
            (a * (e (s a))⁻¹) * ((splitAction s e (s a))
              ((splitCoordinates s e h b).left)).val
          change a * b * (e (s (a * b)))⁻¹ =
            (a * (e (s a))⁻¹) *
              (e (s a) * (b * (e (s b))⁻¹) * (e (s a))⁻¹)
          simp only [map_mul]
          group
        · change s (a * b) = s a * s b
          exact s.map_mul a b }
  refine ⟨q, ?_, ?_, ?_⟩
  · intro a
    rfl
  · intro a
    rfl
  · intro x k
    rfl

#print axioms solution
