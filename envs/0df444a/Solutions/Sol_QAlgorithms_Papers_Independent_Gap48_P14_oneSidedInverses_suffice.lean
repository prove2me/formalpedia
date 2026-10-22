-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P14.oneSidedInverses_suffice
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:25:20.474993+00:00
-- url     : https://prove2.me/submissions/08949be2-1b35-40be-8807-fd652f74d84b

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P14

open QAlgorithms.Papers.Independent.Gap48.P14

open CategoryTheory CategoryTheory.MonoidalCategory

universe u v u1 v1

section Inverses

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

theorem solution
    (h : ∀ x : C, ∃ y : C, Nonempty (y ⊗ x ≅ 𝟙_ C)) :
    ∀ x : C, ∃ y : C, IsWeakInverse x y := by
  intro x
  obtain ⟨y, ⟨e⟩⟩ := h x
  obtain ⟨z, ⟨f⟩⟩ := h y
  -- x ≅ z
  have g : x ≅ z :=
    (λ_ x).symm ≪≫ whiskerRightIso f.symm x ≪≫ α_ z y x ≪≫ whiskerLeftIso z e ≪≫ ρ_ z
  exact ⟨y, ⟨whiskerRightIso g y ≪≫ f⟩, ⟨e⟩⟩

end Inverses
