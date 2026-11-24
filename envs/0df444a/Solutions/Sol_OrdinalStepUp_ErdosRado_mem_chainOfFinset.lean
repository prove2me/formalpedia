-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.mem_chainOfFinset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:48:49.130873+00:00
-- url     : https://prove2.me/submissions/2eea639b-3149-4013-9087-98d840ec4612

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
theorem _root_.solution (𝒯 : Finset SetOrd) (hT : 𝒯.card = n) (i : Fin n) :
    (chainOfFinset 𝒯 hT) i ∈ 𝒯 := by
  rw [← Finset.mem_sort (r := WOle)]
  exact List.get_mem _ _
end OrdinalStepUp.ErdosRado
