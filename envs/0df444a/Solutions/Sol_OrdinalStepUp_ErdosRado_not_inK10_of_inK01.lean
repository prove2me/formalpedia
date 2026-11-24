-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.not_inK10_of_inK01
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:50:10.570665+00:00
-- url     : https://prove2.me/submissions/8976c2b1-2c08-4f49-ac69-2140b84191fe

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
theorem _root_.solution {u : FinChain (n + 3)} (h : InK01 u) : ¬ InK10 u :=
  fun h10 => h10.1 h.1
end OrdinalStepUp.ErdosRado
