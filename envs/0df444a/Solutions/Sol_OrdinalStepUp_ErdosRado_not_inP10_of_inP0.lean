-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.not_inP10_of_inP0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:51:40.52865+00:00
-- url     : https://prove2.me/submissions/655e2162-1b25-4323-b806-59b265cec423

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_inP0_disc01

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution {u : FinChain (n + 4)} (h : InP0 u) : ¬ InP10 u :=
  fun h10 => (asymm (inP0_disc01 h)) h10.2.1
end OrdinalStepUp.ErdosRado
