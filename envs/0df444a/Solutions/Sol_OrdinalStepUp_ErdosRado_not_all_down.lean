-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.not_all_down
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:52:07.823795+00:00
-- url     : https://prove2.me/submissions/0c4ec3a0-9fe9-40d8-a064-511cfcb36df1

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_nonempty_of_otpOf_eq
import Theorems.Thm_OrdinalStepUp_ErdosRado_exists_wo_gt

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution
    (d : wo.α → wo.α → Ordinal) {𝒞 : Set _} (hC : IsIndec (otpOf wo 𝒞))
    (hdown : ∀ a ∈ 𝒞, ∀ b ∈ 𝒞, ∀ c ∈ 𝒞, wo.r a b → wo.r b c → d b c < d a b) : False := by
  set ℰ : SetOrd := {o | ∃ u ∈ 𝒞, ∃ v ∈ 𝒞, wo.r u v ∧ d u v = o} with hE
  obtain ⟨u, hu⟩ := nonempty_of_otpOf_eq hC
  obtain ⟨v, hv, huv⟩ := exists_wo_gt hC hu
  obtain ⟨u₀, hu₀, v₀, hv₀, hu₀v₀, hdeq⟩ : sInf ℰ ∈ ℰ := csInf_mem ⟨d u v, _, hu, _, hv, huv, rfl⟩
  obtain ⟨w, hw, hv₀w⟩ := exists_wo_gt hC hv₀
  have hlt : d v₀ w < sInf ℰ := hdeq ▸ hdown u₀ hu₀ v₀ hv₀ w hw hu₀v₀ hv₀w
  exact absurd hlt (not_lt.2 (csInf_le' ⟨v₀, hv₀, w, hw, hv₀w, rfl⟩))
end OrdinalStepUp.ErdosRado
