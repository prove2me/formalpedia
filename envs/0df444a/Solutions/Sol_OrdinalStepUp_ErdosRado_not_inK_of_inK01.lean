-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.not_inK_of_inK01
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:49:33.960647+00:00
-- url     : https://prove2.me/submissions/02aa16c7-e758-4927-8f27-e09dec0dccf4

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
theorem _root_.solution {u : FinChain (n + 3)} (h : InK01 u) : ¬ (InK0 ⊔ InK1) u :=
  (Or.elim · (h.2 <| · 1) (·  0 h.1))
end OrdinalStepUp.ErdosRado
