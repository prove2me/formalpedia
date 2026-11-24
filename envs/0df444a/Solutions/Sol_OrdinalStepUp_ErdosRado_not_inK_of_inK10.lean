-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.not_inK_of_inK10
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:50:07.754181+00:00
-- url     : https://prove2.me/submissions/032b2356-1663-4d96-a282-d14184065eb9

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
theorem _root_.solution {u : FinChain (n + 3)} (h : InK10 u) : ¬ (InK0 ⊔ InK1) u :=
  fun hK => hK.elim (fun h0 => h.1 (h0 0)) fun h1 => h1 1 h.2
end OrdinalStepUp.ErdosRado
