-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.allUp_of_inP0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:54:33.867809+00:00
-- url     : https://prove2.me/submissions/aab9d113-aad6-47cb-8f3c-82cc65a7159b

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_exists_wo_gt
import Theorems.Thm_OrdinalStepUp_ErdosRado_inP0_disc01
import Theorems.Thm_OrdinalStepUp_ErdosRado_exists_chain_of_four
import Theorems.Thm_OrdinalStepUp_ErdosRado_discSeq_of_four

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution (hA : IsIndec (otp 𝒜))
    (h : ∀ u : FinChain (n + 4), (∀ i, u i ∈ 𝒜) → InP0 u) :
    ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, a ≺w b → b ≺w c → disc a b < disc b c := by
  intro a ha b hb c hc hab hbc
  obtain ⟨e, he, hce⟩ := exists_wo_gt hA hc
  obtain ⟨u, hu, h0, h1, h2, h3⟩ := exists_chain_of_four hA ha hb hc he hab hbc hce
  obtain ⟨d0, d1, _⟩ := discSeq_of_four h0 h1 h2 h3
  have := inP0_disc01 (h u hu)
  rwa [d0, d1] at this
end OrdinalStepUp.ErdosRado
