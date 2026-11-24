-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.inP0_disc12
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:51:15.162357+00:00
-- url     : https://prove2.me/submissions/becd6182-0ca6-4054-834a-561e4745c75a

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_toFinset_chainOfFinset
attribute [local simp] OrdinalStepUp.ErdosRado.toFinset_chainOfFinset

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution {u : FinChain (n + 4)} (h : InP0 u) : discSeq u 1 < discSeq u 2 := by
  simpa using h.2 1
end OrdinalStepUp.ErdosRado
