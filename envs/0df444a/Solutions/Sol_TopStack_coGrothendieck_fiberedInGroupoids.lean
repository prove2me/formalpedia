-- Prove2me | solution 1 for TopStack.coGrothendieck_fiberedInGroupoids
-- status  : ACCEPTED   (prove)
-- author  : @WalrusPaul
-- created : 2026-11-22T18:46:41.221117+00:00
-- url     : https://prove2.me/submissions/881a6163-207f-4a91-900a-62ff008fddca

import Mathlib

open CategoryTheory

set_option autoImplicit false

universe v₁ u₁ v₂ u₂

theorem solution {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂})
    (hF : ∀ S : 𝒮, IsGroupoid (F.obj ⟨Opposite.op S⟩)) :
    (Pseudofunctor.CoGrothendieck.forget F).IsFibered ∧
      ∀ S : 𝒮, IsGroupoid ((Pseudofunctor.CoGrothendieck.forget F).Fiber S) := by
  refine ⟨inferInstance, fun S => ?_⟩
  have := hF S
  exact isGroupoid_of_reflects_iso
    (Functor.Fiber.inducedFunctor (Pseudofunctor.CoGrothendieck.comp_const F S)).inv
