-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P14.unitAutomorphisms_abelian
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:30:18.405967+00:00
-- url     : https://prove2.me/submissions/2f0f4590-36d8-44ed-a55b-257c8902dc75

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P14

open QAlgorithms.Papers.Independent.Gap48.P14

open CategoryTheory CategoryTheory.MonoidalCategory

universe u v u1 v1

theorem g73w_unit_tensor_eq {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (f g : (𝟙_ C ⟶ 𝟙_ C)) :
    (λ_ (𝟙_ C)).inv ≫ (f ⊗ₘ g) ≫ (λ_ (𝟙_ C)).hom = f ≫ g := by
  rw [MonoidalCategory.tensorHom_def, Category.assoc, leftUnitor_naturality, unitors_equal,
    unitors_inv_equal, ← Category.assoc, ← Category.assoc, Category.assoc (ρ_ _).inv,
    rightUnitor_naturality]
  simp

theorem g73w_unit_tensor_eq' {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (f g : (𝟙_ C ⟶ 𝟙_ C)) :
    (λ_ (𝟙_ C)).inv ≫ (f ⊗ₘ g) ≫ (λ_ (𝟙_ C)).hom = g ≫ f := by
  rw [MonoidalCategory.tensorHom_def', Category.assoc, unitors_equal, rightUnitor_naturality,
    ← unitors_equal, ← Category.assoc, ← Category.assoc, Category.assoc (λ_ _).inv,
    leftUnitor_naturality]
  simp

theorem solution
    {C : Type u} [Category.{v} C] [MonoidalCategory C] (h : IsWeakTwoGroup C) :
    (∀ f g : Aut (𝟙_ C), f * g = g * f) ∧
    (∀ f g : (𝟙_ C ⟶ 𝟙_ C),
      (λ_ (𝟙_ C)).inv ≫ (f ⊗ₘ g) ≫ (λ_ (𝟙_ C)).hom = f ≫ g) := by
  refine ⟨fun f g => ?_, g73w_unit_tensor_eq⟩
  apply Iso.ext
  show g.hom ≫ f.hom = f.hom ≫ g.hom
  rw [← g73w_unit_tensor_eq, g73w_unit_tensor_eq']
