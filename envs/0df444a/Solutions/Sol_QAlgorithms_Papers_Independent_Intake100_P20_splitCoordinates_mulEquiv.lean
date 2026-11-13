-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P20.splitCoordinates_mulEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-13T02:45:13.901403+00:00
-- url     : https://prove2.me/submissions/00fe0543-5dca-43be-86e7-133f780cfeb8

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20
import Mathlib.Tactic.Group

open QAlgorithms.Papers.Independent.Intake100.P20

universe u v
theorem solution {A : Type u} {O : Type v} [Group A] [Group O]
    (s : A →* O) (e : O →* A) (h : ∀ x, s (e x) = x) :
    ∃ q : A ≃* SemidirectProduct s.ker O (splitAction s e),
      (∀ a, q a = splitCoordinates s e h a) ∧
      ∀ z, q.symm z = splitAssembly s e z := by
  let q : A ≃* SemidirectProduct s.ker O (splitAction s e) :=
    { toFun := splitCoordinates s e h
      invFun := splitAssembly s e
      left_inv := by
        intro a
        change a * (e (s a))⁻¹ * e (s a) = a
        group
      right_inv := by
        intro z
        apply SemidirectProduct.ext
        · apply Subtype.ext
          change z.left.val * e z.right * (e (s (z.left.val * e z.right)))⁻¹ = z.left.val
          have hz : s z.left.val = 1 := z.left.property
          rw [map_mul,hz,h,one_mul]
          group
        · change s (z.left.val * e z.right) = z.right
          rw [map_mul,z.left.property,h,one_mul]
      map_mul' := by
        intro a b
        apply SemidirectProduct.ext
        · apply Subtype.ext
          change a * b * (e (s (a*b)))⁻¹ =
            (a * (e (s a))⁻¹) *
              (e (s a) * (b * (e (s b))⁻¹) * (e (s a))⁻¹)
          rw [map_mul,map_mul]
          group
        · exact s.map_mul a b }
  exact ⟨q,fun _ => rfl,fun _ => rfl⟩