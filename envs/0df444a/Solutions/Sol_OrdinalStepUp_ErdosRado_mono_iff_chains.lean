-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.mono_iff_chains
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:51:14.519559+00:00
-- url     : https://prove2.me/submissions/574f09a8-b006-4a70-bec8-c7635d60f3f0

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_mem_chainOfFinset
import Theorems.Thm_OrdinalStepUp_ErdosRado_FinChain_mem_toFinset
import Theorems.Thm_OrdinalStepUp_ErdosRado_toFinset_chainOfFinset
attribute [local simp] OrdinalStepUp.ErdosRado.toFinset_chainOfFinset

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution {f : Finset SetOrd → Set.Iio μ} {r : ℕ}
    {ι : Set.Iio μ} :
    Mono f r 𝒜 ι ↔ ∀ u : FinChain r, (∀ j, u j ∈ 𝒜) → f u.toFinset = ι := by
  constructor
  · intro h u hu
    exact h u.toFinset (fun _ hx => by
      obtain ⟨j, rfl⟩ := (FinChain.mem_toFinset u).1 hx
      exact hu j) u.card_toFinset
  · intro h T hTA hTcard
    rw [← toFinset_chainOfFinset T hTcard]
    exact h _ (hTA <| mem_chainOfFinset T hTcard ·)
end OrdinalStepUp.ErdosRado
