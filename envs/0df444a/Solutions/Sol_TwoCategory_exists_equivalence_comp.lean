-- Prove2me | solution 1 for TwoCategory.exists_equivalence_comp
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:58:38.747003+00:00
-- url     : https://prove2.me/submissions/b05e069a-f5ed-4714-8d72-85206891b461

import Mathlib

open CategoryTheory

set_option autoImplicit false

universe w v u

open Bicategory

theorem solution {B : Type u} [Bicategory.{w, v} B] {a b c : B}
    (e₁ : Bicategory.Equivalence a b) (e₂ : Bicategory.Equivalence b c) :
    ∃ e : Bicategory.Equivalence a c, e.hom = e₁.hom ≫ e₂.hom := by
  let eta : 𝟙 a ≅ (e₁.hom ≫ e₂.hom) ≫ (e₂.inv ≫ e₁.inv) :=
    e₁.unit ≪≫ whiskerLeftIso e₁.hom ((λ_ _).symm ≪≫ whiskerRightIso e₂.unit e₁.inv ≪≫ α_ _ _ _)
      ≪≫ (α_ _ _ _).symm
  let eps : (e₂.inv ≫ e₁.inv) ≫ (e₁.hom ≫ e₂.hom) ≅ 𝟙 c :=
    α_ _ _ _ ≪≫ whiskerLeftIso e₂.inv ((α_ _ _ _).symm ≪≫ whiskerRightIso e₁.counit e₂.hom ≪≫ λ_ _)
      ≪≫ e₂.counit
  exact ⟨Bicategory.Equivalence.mkOfAdjointifyCounit eta eps, rfl⟩
