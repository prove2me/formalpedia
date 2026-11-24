-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.otpOf_initial_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:49:38.544711+00:00
-- url     : https://prove2.me/submissions/161a5726-9351-4a04-a153-9c1394f81996

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
theorem _root_.solution {𝒜 : Set _} {x₀ : wo.α} (hx₀ : x₀ ∈ 𝒜) :
    otpOf wo {y ∈ 𝒜 | wo.r y x₀} < otpOf wo 𝒜 := by
  have h : otpOf _ {x ∈ 𝒜 | wo.r x x₀} = typein (Subrel wo.r (· ∈ 𝒜)) ⟨x₀, hx₀⟩ := by
    rw [otpOf, ← type_subrel]
    exact type_eq.2 ⟨⟨⟨fun v ↦ ⟨⟨v.1, v.2.1⟩, v.2.2⟩, fun b ↦ ⟨b.1.1, b.1.2, b.2⟩,
      fun _ ↦ rfl, fun _ ↦ rfl⟩, Iff.rfl⟩⟩
  rw [h, otpOf]
  apply typein_lt_type
end OrdinalStepUp.ErdosRado
