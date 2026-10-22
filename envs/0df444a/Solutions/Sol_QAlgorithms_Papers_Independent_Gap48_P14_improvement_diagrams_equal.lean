-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P14.improvement_diagrams_equal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:37:01.985321+00:00
-- url     : https://prove2.me/submissions/a79d68b6-3c9f-4a9d-a17a-11d98d0fd269

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P14

open QAlgorithms.Papers.Independent.Gap48.P14

open CategoryTheory CategoryTheory.MonoidalCategory

universe u v u1 v1

section Inverses

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

theorem g73w_key (x y : C) (i : 𝟙_ C ≅ x ⊗ y) :
    i.inv ▷ (x ⊗ y) ≫ (α_ (𝟙_ C) x y).inv ≫ (λ_ x).hom ▷ y ≫ i.inv =
      (x ⊗ y) ◁ i.inv ≫ (ρ_ (x ⊗ y)).hom ≫ i.inv := by
  calc
    _ = (i.inv ▷ (x ⊗ y) ≫ 𝟙_ C ◁ i.inv) ≫ (λ_ (𝟙_ C)).hom := by monoidal
    _ = ((x ⊗ y) ◁ i.inv ≫ i.inv ▷ 𝟙_ C) ≫ (ρ_ (𝟙_ C)).hom := by
      rw [whisker_exchange, unitors_equal]
    _ = _ := by monoidal

theorem solution (x y : C) (i : 𝟙_ C ≅ x ⊗ y)
    (e : y ⊗ x ≅ 𝟙_ C) :
    (improvedUnitIso i e).hom = (alternativeUnitIso i e).hom := by
  rw [← cancel_mono i.inv]
  simp only [improvedUnitIso, alternativeUnitIso, Iso.trans_hom, Iso.symm_hom,
    whiskerLeftIso_hom, whiskerRightIso_hom, Category.assoc]
  rw [g73w_key]

end Inverses
