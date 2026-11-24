-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.exists_three_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:50:54.418149+00:00
-- url     : https://prove2.me/submissions/b6ba8115-4d8e-4aa9-93cb-fd3f45418c96

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_otpOf_final_seg_at

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
    ∃ a ∈ 𝒜, ∃ b ∈ 𝒜, ∃ c ∈ 𝒜, wo.r a b ∧ wo.r b c ∧ P a b ∧ ¬ P b c := by
  by_contra hcon
  -- Missing the pattern means `P` propagates one step up any three-chain.
  have hstep : ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, wo.r a b → wo.r b c → P a b → P b c := by
    grind only
  -- `𝒜` itself is not homogeneous, so somewhere `P` does hold on a pair.
  obtain ⟨a, ha, b, hb, hab, hPab⟩ : ∃ a ∈ 𝒜, ∃ b ∈ 𝒜, wo.r a b ∧ P a b := by
    grind only
  -- Its top element then has `P` with everything above it, ...
  have hb_all {c} (hc : c ∈ 𝒜) (hbc : wo.r b c) : P b c := hstep a ha b hb c hc hab hbc hPab
  -- ... and that spreads to every pair of the final segment at `b`.
  refine hD {x ∈ 𝒜 | ¬ wo.r x b} (fun _ hx => hx.1) (otpOf_final_seg_at hA hb) (Or.inl ?_)
  rintro u ⟨huA, hub⟩ v ⟨hvA, -⟩ huv
  rcases trichotomous_of wo.r u b with h | h | h <;> try simp_all
  · exact hstep b hb u huA v hvA h huv (hb_all huA h)
end OrdinalStepUp.ErdosRado
