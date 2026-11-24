-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.disc_lt_disc_of_allUp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:50:38.16813+00:00
-- url     : https://prove2.me/submissions/d46c269a-8692-49ed-9764-90eeb655691f

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
theorem _root_.solution
    (hB : ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, a ≺w b → b ≺w c → disc a b < disc b c)
    {a b c e : SetOrd} (ha : a ∈ 𝒜) (hb : b ∈ 𝒜) (hc : c ∈ 𝒜) (he : e ∈ 𝒜)
    (hab : a ≺w b) (hbc : b = c ∨ b ≺w c) (hce : c ≺w e) : disc a b < disc c e := by
  rcases hbc with rfl | hbc
  · exact hB a ha b hb e he hab hce
  · exact lt_trans (hB a ha b hb c hc hab hbc) (hB b hb c hc e he hbc hce)
end OrdinalStepUp.ErdosRado
