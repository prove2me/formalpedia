-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.not_inP10_of_inP01
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:50:05.097273+00:00
-- url     : https://prove2.me/submissions/006f53e8-3980-4856-806b-aeba36f3d68e

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
theorem _root_.solution {u : FinChain (n + 4)} (h : InP01 u) : ¬ InP10 u :=
  fun h10 => (asymm h10.2.1) h.2.1
end OrdinalStepUp.ErdosRado
