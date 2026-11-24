-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.iterNext_lt_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:52:31.579807+00:00
-- url     : https://prove2.me/submissions/7285f9b3-5a17-431b-a756-c3e2eacf74e8

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_exists_wo_gt
import Theorems.Thm_OrdinalStepUp_ErdosRado_wo_nextIn
import Theorems.Thm_OrdinalStepUp_ErdosRado_toFinset_chainOfFinset
import Theorems.Thm_OrdinalStepUp_ErdosRado_iterNext_mem
attribute [local simp] OrdinalStepUp.ErdosRado.toFinset_chainOfFinset

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution {𝒜 : Set SetOrd} {x : SetOrd} (hA : IsIndec (otp 𝒜))
    (hx : x ∈ 𝒜) (k : ℕ) :
    iterNext 𝒜 x k ≺w iterNext 𝒜 x (k + 1) := by
  simp only [iterNext, Function.iterate_succ_apply']
  exact wo_nextIn (exists_wo_gt hA (iterNext_mem hA hx k))
end OrdinalStepUp.ErdosRado
