-- Prove2me | solution 1 for TopStack.Inertia.forget_isEquivalence_iff
-- status  : ACCEPTED   (prove)
-- author  : @WalrusPaul
-- created : 2026-11-22T18:26:21.268491+00:00
-- url     : https://prove2.me/submissions/1f0e8788-85a4-4c61-be98-be4a6ada7006

import Mathlib
import Definitions.Def_TopStack_Inertia

open CategoryTheory

set_option autoImplicit false

universe v₁ u₁ v₂ u₂

theorem solution {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    {𝒳 : Type u₂} [Category.{v₂} 𝒳] (p : 𝒳 ⥤ 𝒮) :
    (TopStack.Inertia.forget p).IsEquivalence ↔
      ∀ (x : 𝒳) (f : x ≅ x), p.map f.hom = 𝟙 (p.obj x) → f.hom = 𝟙 x := by
  constructor
  · -- An equivalence is full: the identity of `x` lifts to a morphism `(x, f) ⟶ (x, 𝟙)`.
    intro hE x f hf
    have hfull : (TopStack.Inertia.forget p).Full := hE.full
    let a : TopStack.Inertia p := ⟨x, f, hf⟩
    let b : TopStack.Inertia p := ⟨x, Iso.refl x, by simp⟩
    obtain ⟨φ, hφ⟩ := (TopStack.Inertia.forget p).map_surjective (X := a) (Y := b) (𝟙 x)
    have h1 : f.hom ≫ (φ.1 : x ⟶ x) = (φ.1 : x ⟶ x) ≫ (𝟙 x : x ⟶ x) := φ.2
    have h2 : (φ.1 : x ⟶ x) = 𝟙 x := hφ
    rw [h2, Category.comp_id, Category.comp_id] at h1
    exact h1
  · -- Every object of the inertia category is `(x, 𝟙)`, so `forget` is full, faithful and
    -- essentially surjective.
    intro h
    have hfaith : (TopStack.Inertia.forget p).Faithful :=
      ⟨fun {a b} φ ψ hφψ => Subtype.ext hφψ⟩
    have hfull : (TopStack.Inertia.forget p).Full := by
      refine ⟨fun {a b} φ => ?_⟩
      have ha : a.aut.hom = 𝟙 a.obj := h a.obj a.aut a.map_aut_hom
      have hb : b.aut.hom = 𝟙 b.obj := h b.obj b.aut b.map_aut_hom
      refine ⟨⟨φ, ?_⟩, rfl⟩
      rw [ha, hb]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
    have hess : (TopStack.Inertia.forget p).EssSurj :=
      ⟨fun x => ⟨⟨x, Iso.refl x, by simp⟩, ⟨Iso.refl x⟩⟩⟩
    exact { faithful := hfaith, full := hfull, essSurj := hess }
