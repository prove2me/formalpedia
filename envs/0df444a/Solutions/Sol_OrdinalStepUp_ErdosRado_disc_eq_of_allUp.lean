-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.disc_eq_of_allUp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:49:55.89765+00:00
-- url     : https://prove2.me/submissions/119dcb84-2040-47cf-9948-48152196abde

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_disc_eq_of_disc_lt_disc

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution
    (hB : ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, a ≺w b → b ≺w c → disc a b < disc b c)
    (ha : a ∈ 𝒜) (hb : b ∈ 𝒜) (hc : c ∈ 𝒜)
    (hab : a ≺w b) (hbc : b ≺w c) : disc a c = disc a b :=
  disc_eq_of_disc_lt_disc (fun h => irrefl _ (h ▸ hab)) (hB a ha b hb c hc hab hbc)
end OrdinalStepUp.ErdosRado
