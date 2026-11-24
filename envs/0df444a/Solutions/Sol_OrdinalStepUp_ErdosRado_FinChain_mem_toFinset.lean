-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.FinChain.mem_toFinset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:48:00.043507+00:00
-- url     : https://prove2.me/submissions/cec44340-6d40-4a9e-9504-95298706530f

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
namespace FinChain
theorem _root_.solution (u : FinChain n) {x : SetOrd} :
    x ∈ u.toFinset ↔ ∃ i, u i = x := by
  simp [FinChain.toFinset]
end FinChain
end OrdinalStepUp.ErdosRado
