-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P14.triangle_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:33:46.236661+00:00
-- url     : https://prove2.me/submissions/d3abb15a-bddd-4f2d-954b-78ef753f5e01

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P14

open QAlgorithms.Papers.Independent.Gap48.P14

open CategoryTheory CategoryTheory.MonoidalCategory

universe u v u1 v1

section Inverses

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

theorem g73w_first_of_second (x y : C) (i : 𝟙_ C ≅ x ⊗ y)
    (e : y ⊗ x ≅ 𝟙_ C) (h : SecondTriangle i e) : FirstTriangle i e := by
  unfold SecondTriangle at h
  unfold FirstTriangle
  have idem : (i.hom ▷ x ≫ (α_ x y x).hom ≫ x ◁ e.hom) ≫ ((ρ_ x).hom ≫ (λ_ x).inv) ≫
      (i.hom ▷ x ≫ (α_ x y x).hom ≫ x ◁ e.hom) =
      (i.hom ▷ x ≫ (α_ x y x).hom ≫ x ◁ e.hom) := by
    calc
      _ = i.hom ▷ x ⊗≫ (𝟙_ C ◁ (x ◁ e.hom) ≫ i.hom ▷ (x ⊗ 𝟙_ C)) ⊗≫ x ◁ e.hom := by
        monoidal
      _ = i.hom ▷ x ⊗≫ (i.hom ▷ (x ⊗ (y ⊗ x)) ≫ (x ⊗ y) ◁ (x ◁ e.hom)) ⊗≫ x ◁ e.hom := by
        rw [whisker_exchange]
      _ = 𝟙 _ ⊗≫ (𝟙_ C ◁ i.hom ≫ i.hom ▷ (x ⊗ y)) ▷ x ⊗≫
            x ◁ ((y ⊗ x) ◁ e.hom ≫ e.hom ▷ 𝟙_ C) ⊗≫ 𝟙 _ := by
        monoidal
      _ = 𝟙 _ ⊗≫ (i.hom ▷ 𝟙_ C ≫ (x ⊗ y) ◁ i.hom) ▷ x ⊗≫
            x ◁ (e.hom ▷ (y ⊗ x) ≫ 𝟙_ C ◁ e.hom) ⊗≫ 𝟙 _ := by
        rw [whisker_exchange i.hom i.hom, whisker_exchange e.hom e.hom]
      _ = i.hom ▷ x ⊗≫ x ◁ (y ◁ i.hom ≫ (α_ y x y).inv ≫ e.hom ▷ y) ▷ x ⊗≫ x ◁ e.hom := by
        monoidal
      _ = _ := by
        rw [h]; monoidal
  rw [← cancel_epi ((i.hom ▷ x ≫ (α_ x y x).hom ≫ x ◁ e.hom) ≫ (ρ_ x).hom ≫ (λ_ x).inv)]
  rw [Category.assoc, idem]
  simp

theorem g73w_second_of_first (x y : C) (i : 𝟙_ C ≅ x ⊗ y)
    (e : y ⊗ x ≅ 𝟙_ C) (h : FirstTriangle i e) : SecondTriangle i e := by
  unfold SecondTriangle
  unfold FirstTriangle at h
  have idem : (y ◁ i.hom ≫ (α_ y x y).inv ≫ e.hom ▷ y) ≫ ((λ_ y).hom ≫ (ρ_ y).inv) ≫
      (y ◁ i.hom ≫ (α_ y x y).inv ≫ e.hom ▷ y) =
      (y ◁ i.hom ≫ (α_ y x y).inv ≫ e.hom ▷ y) := by
    calc
      _ = y ◁ i.hom ⊗≫ ((e.hom ▷ y ▷ 𝟙_ C) ≫ (𝟙_ C ⊗ y) ◁ i.hom) ⊗≫ e.hom ▷ y := by
        monoidal
      _ = 𝟙 _ ⊗≫ y ◁ (i.hom ▷ 𝟙_ C ≫ (x ⊗ y) ◁ i.hom) ⊗≫
            (e.hom ▷ (y ⊗ x) ≫ 𝟙_ C ◁ e.hom) ▷ y ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]; monoidal
      _ = y ◁ i.hom ⊗≫ y ◁ (i.hom ▷ x ≫ (α_ x y x).hom ≫ x ◁ e.hom) ▷ y ⊗≫ e.hom ▷ y := by
        rw [← whisker_exchange, ← whisker_exchange]; monoidal
      _ = _ := by
        rw [h]; monoidal
  rw [← cancel_epi ((y ◁ i.hom ≫ (α_ y x y).inv ≫ e.hom ▷ y) ≫ (λ_ y).hom ≫ (ρ_ y).inv)]
  rw [Category.assoc, idem]
  simp

theorem solution (x y : C) (i : 𝟙_ C ≅ x ⊗ y)
    (e : y ⊗ x ≅ 𝟙_ C) :
    FirstTriangle i e ↔ SecondTriangle i e :=
  ⟨g73w_second_of_first x y i e, g73w_first_of_second x y i e⟩

end Inverses
