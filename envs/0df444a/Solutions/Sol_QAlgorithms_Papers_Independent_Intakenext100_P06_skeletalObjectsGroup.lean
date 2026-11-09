-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P06.skeletalObjectsGroup
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T11:30:01.247884+00:00
-- url     : https://prove2.me/submissions/40454f75-9e0c-4753-804b-c1893fbc25b9

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P06

open CategoryTheory CategoryTheory.MonoidalCategory

universe u v u1 v1 w

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P06.singletonSymmetric

open QAlgorithms.Papers.Independent.Intakenext100.P06 QAlgorithms.Papers.Independent.Gap48.P14
  QAlgorithms.Papers.Independent.Renew46.P18 in
theorem solution {C : Type u} [Category.{v} C]
    [MonoidalCategory C] (h : IsWeakTwoGroup C) (hs : Skeletal C) :
    ∃ k : Group C,
      letI := k
      (∀ x y : C, x * y = x ⊗ y) ∧ (1 : C) = 𝟙_ C ∧
      (∀ x y : C, IsWeakInverse x y → x⁻¹ = y) := by
  let k : Group C :=
    { mul := fun x y => x ⊗ y
      one := 𝟙_ C
      inv := fun x => Classical.choose (h.2 x)
      mul_assoc := fun x y z => hs (Nonempty.intro (α_ x y z))
      one_mul := fun x => hs (Nonempty.intro (λ_ x))
      mul_one := fun x => hs (Nonempty.intro (ρ_ x))
      inv_mul_cancel := fun x => hs (Classical.choose_spec (h.2 x)).2 }
  refine ⟨k, ?_⟩
  refine ⟨fun x y => rfl, rfl, fun x y hxy => ?_⟩
  exact inv_eq_of_mul_eq_one_right (hs hxy.1)
