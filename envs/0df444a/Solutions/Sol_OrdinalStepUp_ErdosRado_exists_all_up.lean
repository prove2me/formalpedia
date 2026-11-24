-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.exists_all_up
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:52:42.461967+00:00
-- url     : https://prove2.me/submissions/b90a866d-6ca1-4abd-937f-2c00b4d70da2

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_otpOf_gt_seg
import Theorems.Thm_OrdinalStepUp_ErdosRado_not_all_down

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution
    (d : wo.α → wo.α → Ordinal) {𝒜 : Set _} (hA : IsIndec (otpOf wo 𝒜))
    (hne : ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, wo.r a b → wo.r b c → d a b ≠ d b c)
    (h : (∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, ∀ e ∈ 𝒜, wo.r a b → wo.r b c → wo.r c e →
            d a b < d b c → d b c < d c e) ∨
         (∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, ∀ e ∈ 𝒜, wo.r a b → wo.r b c → wo.r c e →
            d b c < d a b → d c e < d b c)) :
    ∃ ℬ ⊆ 𝒜, otpOf wo ℬ = otpOf wo 𝒜 ∧
      ∀ a ∈ ℬ, ∀ b ∈ ℬ, ∀ c ∈ ℬ, wo.r a b → wo.r b c → d a b < d b c := by
  rcases h with hi | hii
  · -- Case (i). Some triple goes up, ...
    obtain ⟨a, ha, b, hb, c, hc, hab, hbc, hup⟩ :
        ∃ a ∈ 𝒜, ∃ b ∈ 𝒜, ∃ c ∈ 𝒜, wo.r a b ∧ wo.r b c ∧ d a b < d b c := by
      by_contra hno
      refine not_all_down d hA (fun a ha b hb c hc hab hbc => ?_)
      exact ((lt_trichotomy (d a b) (d b c)).resolve_left
        (fun h1 => hno ⟨a, ha, b, hb, c, hc, hab, hbc, h1⟩)).resolve_left
        (hne a ha b hb c hc hab hbc)
    -- ... and shifting the window one step at a time carries `up` past `c`.
    have h1 : ∀ e ∈ 𝒜, wo.r c e → d b c < d c e :=
      fun e he hce => hi _ ha _ hb _ hc _ he hab hbc hce hup
    have h2 : ∀ u ∈ 𝒜, ∀ v ∈ 𝒜, wo.r c u → wo.r u v → d c u < d u v :=
      fun u hu v hv hcu huv => hi b hb c hc u hu v hv hbc hcu huv (h1 u hu hcu)
    have h3 : ∀ u ∈ 𝒜, ∀ v ∈ 𝒜, ∀ w ∈ 𝒜, wo.r c u → wo.r u v → wo.r v w → d u v < d v w :=
      fun u hu v hv w hw hcu huv hvw => hi c hc u hu v hv w hw hcu huv hvw (h2 u hu v hv hcu huv)
    exact ⟨{x ∈ 𝒜 | wo.r c x}, fun _ hx => hx.1, otpOf_gt_seg hA hc,
      fun u hu v hv w hw huv hvw => h3 u hu.1 v hv.1 w hw.1 hu.2 huv hvw⟩
  · -- Case (ii). A single `down` triple would spread over a whole final segment.
    refine ⟨𝒜, subset_rfl, rfl, fun a ha b hb c hc hab hbc => ?_⟩
    rcases lt_trichotomy (d a b) (d b c) with h1 | h1 | h1
    · exact h1
    · exact absurd h1 (hne a ha b hb c hc hab hbc)
    · exfalso
      have k1 : ∀ e ∈ 𝒜, wo.r c e → d c e < d b c :=
        (hii a ha b hb c hc · · hab hbc · h1)
      have k2 : ∀ u ∈ 𝒜, ∀ v ∈ 𝒜, wo.r c u → wo.r u v → d u v < d c u :=
        fun u hu v hv hcu huv => hii b hb c hc u hu v hv hbc hcu huv (k1 u hu hcu)
      have k3 : ∀ u ∈ 𝒜, ∀ v ∈ 𝒜, ∀ w ∈ 𝒜, wo.r c u → wo.r u v → wo.r v w → d v w < d u v :=
        fun u hu v hv w hw hcu huv hvw => hii c hc u hu v hv w hw hcu huv hvw (k2 u hu v hv hcu huv)
      exact not_all_down d ((otpOf_gt_seg hA hc) ▸ hA)
        (fun u hu v hv w hw huv hvw => k3 u hu.1 v hv.1 w hw.1 hu.2 huv hvw)
end OrdinalStepUp.ErdosRado
