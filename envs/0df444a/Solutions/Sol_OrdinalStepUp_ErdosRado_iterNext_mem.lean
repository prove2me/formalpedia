-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.iterNext_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:52:07.10739+00:00
-- url     : https://prove2.me/submissions/f8c216dd-9b73-4d1e-b31b-2372bdfb84c4

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_exists_wo_gt
import Theorems.Thm_OrdinalStepUp_ErdosRado_nextIn_mem
import Theorems.Thm_OrdinalStepUp_ErdosRado_toFinset_chainOfFinset
attribute [local simp] OrdinalStepUp.ErdosRado.toFinset_chainOfFinset

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution {𝒜 : Set SetOrd} {x : SetOrd} (hA : IsIndec (otp 𝒜))
    (hx : x ∈ 𝒜) : ∀ k, iterNext 𝒜 x k ∈ 𝒜
  | 0 => hx
  | k + 1 => by
      simp only [iterNext, Function.iterate_succ_apply']
      exact nextIn_mem (exists_wo_gt hA (solution hA hx k))
end OrdinalStepUp.ErdosRado
