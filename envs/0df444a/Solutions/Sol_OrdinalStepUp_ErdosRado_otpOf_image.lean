-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.otpOf_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:49:57.015803+00:00
-- url     : https://prove2.me/submissions/57324d72-04d2-4a7a-a4e2-edf355aa2390

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution {𝒜 : Set _} {f} (hf : ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, wo.r a b → wo'.r (f a) (f b)) :
    otpOf wo' (f '' 𝒜) = otpOf wo 𝒜 := by
  have hmono : ∀ a b : {x // x ∈ 𝒜}, Subrel wo.r (· ∈ 𝒜) a b →
      Subrel wo'.r (· ∈ f '' 𝒜) ⟨f a.1, a.1, a.2, rfl⟩ ⟨f b.1, b.1, b.2, rfl⟩ :=
    fun a b => hf a.1 a.2 b.1 b.2
  refine type_eq.2 ⟨(RelIso.ofSurjective (RelEmbedding.ofMonotone _ hmono) ?_).symm⟩
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩
end OrdinalStepUp.ErdosRado
