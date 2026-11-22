-- Prove2me | solution 1 for TwoCategory.exists_equivalence_of_quasiInverses
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:56:41.588872+00:00
-- url     : https://prove2.me/submissions/4c69d9c9-fe0b-482a-9825-aae44c8f94a8

import Mathlib

open CategoryTheory

set_option autoImplicit false

universe w v u

open CategoryTheory.Bicategory

theorem solution {B : Type u} [Bicategory.{w, v} B] {a b : B}
    (f : a ⟶ b) (g h : b ⟶ a) (α : 𝟙 a ≅ f ≫ g) (β : h ≫ f ≅ 𝟙 b) :
    ∃ e : Bicategory.Equivalence a b, e.hom = f ∧ e.inv = g := by
  -- `g ≅ h`: `g ≅ 𝟙 ≫ g ≅ (h ≫ f) ≫ g ≅ h ≫ (f ≫ g) ≅ h ≫ 𝟙 ≅ h`
  let γ : g ≅ h := (λ_ g).symm ≪≫ whiskerRightIso β.symm g ≪≫ α_ h f g ≪≫
    whiskerLeftIso h α.symm ≪≫ ρ_ h
  -- a counit for `g`: `g ≫ f ≅ h ≫ f ≅ 𝟙 b`
  let eps : g ≫ f ≅ 𝟙 b := whiskerRightIso γ f ≪≫ β
  exact ⟨Bicategory.Equivalence.mkOfAdjointifyCounit α eps, rfl, rfl⟩
