-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.up_forces_up_of_no_inP01
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:54:32.737415+00:00
-- url     : https://prove2.me/submissions/c472f353-1967-4dc8-9021-03cc9e3a744a

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_disc_ne_of_homogeneous
import Theorems.Thm_OrdinalStepUp_ErdosRado_inK_of_homog
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
    (hom : HomAgree 𝒜)
    (h : ∀ u : FinChain (n + 4), (∀ i, u i ∈ 𝒜) → ¬ InP01 u) :
    ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, ∀ e ∈ 𝒜, a ≺w b → b ≺w c → c ≺w e →
      disc a b < disc b c → disc b c < disc c e := by
  intro a ha b hb c hc e he hab hbc hce hup
  by_contra! hcon
  obtain ⟨u, hu, h0, h1, h2, h3⟩ := exists_chain_of_four hA ha hb hc he hab hbc hce
  obtain ⟨d0, d1, d2⟩ := discSeq_of_four h0 h1 h2 h3
  refine h u hu ⟨inK_of_homog hom hu, by rw [d0, d1]; exact hup, ?_⟩
  rw [d1, d2]
  exact lt_of_le_of_ne hcon (disc_ne_of_homogeneous hom hb hc he hbc hce).symm
end OrdinalStepUp.ErdosRado
