-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.toFinset_chainOfFinset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:50:37.163454+00:00
-- url     : https://prove2.me/submissions/fc8abd44-3530-4e5a-9fec-38dbdee17514

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_mem_chainOfFinset
import Theorems.Thm_OrdinalStepUp_ErdosRado_exists_eq_chainOfFinset
import Theorems.Thm_OrdinalStepUp_ErdosRado_FinChain_mem_toFinset

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution (𝒯 : Finset SetOrd) (hT : 𝒯.card = n) :
    (chainOfFinset 𝒯 hT).toFinset = 𝒯 := by
  ext x
  rw [FinChain.mem_toFinset]
  exact ⟨fun ⟨i, hi⟩ => hi ▸ mem_chainOfFinset 𝒯 hT i, exists_eq_chainOfFinset 𝒯 hT⟩
end OrdinalStepUp.ErdosRado
