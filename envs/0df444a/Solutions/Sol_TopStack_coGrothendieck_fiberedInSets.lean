-- Prove2me | solution 1 for TopStack.coGrothendieck_fiberedInSets
-- status  : ACCEPTED   (prove)
-- author  : @WalrusPaul
-- created : 2026-11-22T18:47:39.124181+00:00
-- url     : https://prove2.me/submissions/0db9a10a-3aa1-4d3a-b0a9-73268ba09800

import Mathlib

open CategoryTheory

set_option autoImplicit false

universe v₁ u₁ v₂ u₂

theorem solution {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂})
    (hF : ∀ S : 𝒮, IsDiscrete (F.obj ⟨Opposite.op S⟩)) :
    (Pseudofunctor.CoGrothendieck.forget F).IsFibered ∧
      ∀ S : 𝒮, IsDiscrete ((Pseudofunctor.CoGrothendieck.forget F).Fiber S) := by
  refine ⟨inferInstance, fun S => ?_⟩
  have hS := hF S
  let E := Functor.Fiber.inducedFunctor (Pseudofunctor.CoGrothendieck.comp_const F S)
  have surj : ∀ Y : (Pseudofunctor.CoGrothendieck.forget F).Fiber S, ∃ a, E.obj a = Y := by
    rintro ⟨⟨B, x⟩, h⟩
    change B = S at h
    subst h
    exact ⟨x, rfl⟩
  refine { subsingleton := fun X Y => ⟨fun f g => ?_⟩, eq_of_hom := ?_ }
  · obtain ⟨a, rfl⟩ := surj X
    obtain ⟨b, rfl⟩ := surj Y
    rw [← E.map_preimage f, ← E.map_preimage g, Subsingleton.elim (E.preimage f) (E.preimage g)]
  · intro X Y f
    obtain ⟨a, rfl⟩ := surj X
    obtain ⟨b, rfl⟩ := surj Y
    rw [IsDiscrete.eq_of_hom (E.preimage f)]
