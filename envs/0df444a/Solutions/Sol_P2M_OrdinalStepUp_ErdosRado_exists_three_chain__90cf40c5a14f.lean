-- Prove2me | solution 1 for P2M_OrdinalStepUp_ErdosRado_exists_three_chain__90cf40c5a14f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:51:31.342867+00:00
-- url     : https://prove2.me/submissions/fb678795-ac13-45fe-9b65-ec7d58259bc0

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_exists_three_chain

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution
    (P : wo.α → wo.α → Prop) {𝒜 : Set wo.α} (hA : IsIndec (otpOf wo 𝒜))
    (hD : ∀ ℬ, ℬ ⊆ 𝒜 → otpOf wo ℬ = otpOf wo 𝒜 →
      ¬ ((∀ u ∈ ℬ, ∀ v ∈ ℬ, wo.r u v → P u v) ∨ (∀ u ∈ ℬ, ∀ v ∈ ℬ, wo.r u v → ¬ P u v))) :
    ∃ a ∈ 𝒜, ∃ b ∈ 𝒜, ∃ c ∈ 𝒜, wo.r a b ∧ wo.r b c ∧ ¬ P a b ∧ P b c := by
  have := exists_three_chain (¬ P · · ) hA (by grind only)
  simp_all
end OrdinalStepUp.ErdosRado
