-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.no_pattern01_of_no_inK01
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:54:29.909601+00:00
-- url     : https://prove2.me/submissions/b084eb58-6026-46eb-adab-cdc28479d73e

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_exists_wo_gt
import Theorems.Thm_OrdinalStepUp_ErdosRado_exists_chain_of_four
import Theorems.Thm_OrdinalStepUp_ErdosRado_agreeAt_of_four

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution (hA : IsIndec (otp 𝒜))
    (h : ∀ u : FinChain (n + 4), (∀ i, u i ∈ 𝒜) → ¬ InK01 u) :
    ¬ ∃ a ∈ 𝒜, ∃ b ∈ 𝒜, ∃ c ∈ 𝒜, a ≺w b ∧ b ≺w c ∧ a ≺ b ∧ ¬ b ≺ c := by
  rintro ⟨a, ha, b, hb, c, hc, hab, hbc, hag, hdis⟩
  obtain ⟨d, hd, hcd⟩ := exists_wo_gt hA hc
  obtain ⟨u, hu, h0, h1, h2, _⟩ := exists_chain_of_four hA ha hb hc hd hab hbc hcd
  obtain ⟨e0, e1⟩ := agreeAt_of_four h0 h1 h2
  exact h u hu ⟨e0.2 hag, hdis ∘ e1.1⟩
end OrdinalStepUp.ErdosRado
