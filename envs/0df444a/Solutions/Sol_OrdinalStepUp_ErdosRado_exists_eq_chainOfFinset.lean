-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.exists_eq_chainOfFinset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:50:01.614831+00:00
-- url     : https://prove2.me/submissions/b886af10-0618-4807-9bb0-fe9e439fcf07

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
theorem _root_.solution (𝒯 : Finset SetOrd) (hT : 𝒯.card = n)
    (ha : a ∈ 𝒯) : ∃ i, (chainOfFinset 𝒯 hT) i = a := by
  obtain ⟨k, hk⟩ := List.mem_iff_get.1 ((Finset.mem_sort (r := WOle)).2 ha)
  refine ⟨k.cast (by rw [Finset.length_sort, hT]), by rw [← hk]; rfl⟩
end OrdinalStepUp.ErdosRado
