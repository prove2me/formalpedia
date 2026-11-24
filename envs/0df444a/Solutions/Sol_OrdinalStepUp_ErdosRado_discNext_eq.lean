-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.discNext_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:50:25.532193+00:00
-- url     : https://prove2.me/submissions/7369b8ba-73c9-4305-b905-56e675fea8db

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_disc_eq_of_allUp
import Theorems.Thm_OrdinalStepUp_ErdosRado_nextIn_mem
import Theorems.Thm_OrdinalStepUp_ErdosRado_wo_nextIn
import Theorems.Thm_OrdinalStepUp_ErdosRado_nextIn_le

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution
    (hup : ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, a ≺w b → b ≺w c → disc a b < disc b c)
    (ha : a ∈ 𝒜) (hb : b ∈ 𝒜) (hab : a ≺w b) :
    discNext 𝒜 a = disc a b := by
  have hex : ∃ b, b ∈ 𝒜 ∧ a ≺w b := ⟨b, hb, hab⟩
  rcases nextIn_le hex hb hab with heq | hlt
  · rw [discNext, heq]
  · exact (disc_eq_of_allUp hup ha (nextIn_mem hex) hb (wo_nextIn hex) hlt).symm
end OrdinalStepUp.ErdosRado
