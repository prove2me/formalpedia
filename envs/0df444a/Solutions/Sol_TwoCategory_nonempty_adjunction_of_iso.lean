-- Prove2me | solution 1 for TwoCategory.nonempty_adjunction_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:03:41.783804+00:00
-- url     : https://prove2.me/submissions/519627a9-da62-4855-aa57-002c8dc1d63f

import Mathlib

open CategoryTheory

set_option autoImplicit false

universe w v u

namespace Sol_TwoCategory_nonempty_adjunction_of_iso

open Bicategory

variable {B : Type u} [Bicategory.{w, v} B] {a b : B}

/-- Transport of an adjunction along a 2-isomorphism of the left adjoint. -/
def adjOfIsoLeft {f f' : a ⟶ b} {g : b ⟶ a} (adj : Bicategory.Adjunction f g) (α : f ≅ f') :
    Bicategory.Adjunction f' g where
  unit := adj.unit ≫ α.hom ▷ g
  counit := g ◁ α.inv ≫ adj.counit
  left_triangle := by
    calc
      _ = adj.unit ▷ f' ⊗≫ (α.hom ▷ (g ≫ f') ≫ f' ◁ g ◁ α.inv) ⊗≫ f' ◁ adj.counit := by
        bicategory
      _ = adj.unit ▷ f' ⊗≫ (f ≫ g) ◁ α.inv ⊗≫ (α.hom ▷ (g ≫ f) ≫ f' ◁ adj.counit) := by
        rw [← whisker_exchange α.hom (g ◁ α.inv)]; bicategory
      _ = (adj.unit ▷ f' ≫ (f ≫ g) ◁ α.inv) ⊗≫ f ◁ adj.counit ⊗≫ α.hom ▷ 𝟙 b := by
        rw [← whisker_exchange α.hom adj.counit]; bicategory
      _ = 𝟙 a ◁ α.inv ⊗≫ (adj.unit ▷ f ⊗≫ f ◁ adj.counit) ⊗≫ α.hom ▷ 𝟙 b := by
        rw [← whisker_exchange adj.unit α.inv]; bicategory
      _ = _ := by
        rw [← leftZigzag, adj.left_triangle]
        simp [bicategoricalComp]
  right_triangle := by
    calc
      _ = g ◁ adj.unit ⊗≫ ((g ◁ α.hom ≫ g ◁ α.inv) ▷ g) ⊗≫ adj.counit ▷ g := by
        bicategory
      _ = g ◁ adj.unit ⊗≫ adj.counit ▷ g := by
        rw [← whiskerLeft_comp, α.hom_inv_id]; bicategory
      _ = _ := by
        rw [← rightZigzag, adj.right_triangle]

/-- Transport of an adjunction along a 2-isomorphism of the right adjoint. -/
def adjOfIsoRight {f : a ⟶ b} {g g' : b ⟶ a} (adj : Bicategory.Adjunction f g) (β : g ≅ g') :
    Bicategory.Adjunction f g' where
  unit := adj.unit ≫ f ◁ β.hom
  counit := β.inv ▷ f ≫ adj.counit
  left_triangle := by
    calc
      _ = adj.unit ▷ f ⊗≫ f ◁ ((β.hom ≫ β.inv) ▷ f) ⊗≫ f ◁ adj.counit := by
        bicategory
      _ = adj.unit ▷ f ⊗≫ f ◁ adj.counit := by
        rw [β.hom_inv_id]; bicategory
      _ = _ := by
        rw [← leftZigzag, adj.left_triangle]
  right_triangle := by
    calc
      _ = g' ◁ adj.unit ⊗≫ (g' ◁ f ◁ β.hom ≫ β.inv ▷ (f ≫ g')) ⊗≫ adj.counit ▷ g' := by
        bicategory
      _ = (g' ◁ adj.unit ≫ β.inv ▷ (f ≫ g)) ⊗≫ ((g ≫ f) ◁ β.hom ≫ adj.counit ▷ g') := by
        rw [whisker_exchange β.inv (f ◁ β.hom)]; bicategory
      _ = β.inv ▷ 𝟙 a ⊗≫ (g ◁ adj.unit ⊗≫ adj.counit ▷ g) ⊗≫ 𝟙 b ◁ β.hom := by
        rw [whisker_exchange β.inv adj.unit, whisker_exchange adj.counit β.hom]; bicategory
      _ = _ := by
        rw [← rightZigzag, adj.right_triangle]
        simp [bicategoricalComp]

end Sol_TwoCategory_nonempty_adjunction_of_iso



theorem solution {B : Type u} [Bicategory.{w, v} B] {a b : B}
    {f f' : a ⟶ b} {g g' : b ⟶ a} (adj : Bicategory.Adjunction f g) (α : f ≅ f') (β : g ≅ g') :
    Nonempty (Bicategory.Adjunction f' g') :=
  ⟨Sol_TwoCategory_nonempty_adjunction_of_iso.adjOfIsoRight
    (Sol_TwoCategory_nonempty_adjunction_of_iso.adjOfIsoLeft adj α) β⟩
