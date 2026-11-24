-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.not_inP01_of_inP0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:51:39.879815+00:00
-- url     : https://prove2.me/submissions/ce2edaf9-1c7b-435f-a383-142a29111ea9

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_inP0_disc12

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution {u : FinChain (n + 4)} (h : InP0 u) : ¬ InP01 u :=
  fun h01 => (asymm (inP0_disc12 h)) h01.2.2
end OrdinalStepUp.ErdosRado
