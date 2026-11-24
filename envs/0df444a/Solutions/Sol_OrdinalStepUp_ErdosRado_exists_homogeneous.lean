-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.exists_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:51:55.507204+00:00
-- url     : https://prove2.me/submissions/cae0dc39-5a70-4340-b602-d6ca3959e586

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_agree_iff_lexLT
import Theorems.Thm_OrdinalStepUp_ErdosRado_agree_comm
import Theorems.Thm_OrdinalStepUp_ErdosRado_exists_three_chain
import Theorems.Thm_P2M_OrdinalStepUp_ErdosRado_exists_three_chain__90cf40c5a14f

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution (hA : IsIndec (otp 𝒜))
    (h : (¬ ∃ a ∈ 𝒜, ∃ b ∈ 𝒜, ∃ c ∈ 𝒜, a ≺w b ∧ b ≺w c ∧ a ≺ b ∧ ¬ b ≺ c) ∨
         (¬ ∃ a ∈ 𝒜, ∃ b ∈ 𝒜, ∃ c ∈ 𝒜, a ≺w b ∧ b ≺w c ∧ ¬ a ≺ b ∧ b ≺ c)) :
    ∃ ℬ ⊆ 𝒜, otp ℬ = otp 𝒜 ∧ HomAgree ℬ := by
  by_contra hcon
  have hcon : ∀ ℬ, ℬ ⊆ 𝒜 → otp ℬ = otp 𝒜 →
      ¬ ((∀ u ∈ ℬ, ∀ v ∈ ℬ, u ≺w v → u ≺ v) ∨
         (∀ u ∈ ℬ, ∀ v ∈ ℬ, u ≺w v → ¬ u ≺ v)) := fun ℬ h1 h2 hor => hcon ⟨ℬ, h1, h2, by
    rcases hor with hag | hdis
    · left
      intro u hu v hv hne
      rcases trichotomous_of WO.r u v with huv | rfl | hvu
      · exact (agree_iff_lexLT huv).2 (hag u hu v hv huv)
      · exact absurd rfl hne
      · exact agree_comm.2 ((agree_iff_lexLT hvu).2 (hag v hv u hu hvu))
    · right
      intro u hu v hv hne
      rcases trichotomous_of WO.r u v with huv | rfl | hvu
      · exact mt (agree_iff_lexLT huv).1 (hdis u hu v hv huv)
      · exact absurd rfl hne
      · exact fun hag => mt (agree_iff_lexLT hvu).1 (hdis v hv u hu hvu) (agree_comm.1 hag)⟩
  rcases h with h1 | h2
  · exact h1 (exists_three_chain (· ≺ ·) hA hcon)
  · exact h2 (exists_three_chain' (· ≺ ·) hA hcon)
end OrdinalStepUp.ErdosRado
