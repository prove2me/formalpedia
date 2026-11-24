-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.otpOf_final_seg_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:50:29.249194+00:00
-- url     : https://prove2.me/submissions/dbec0869-5d7f-4a01-9c48-668c58c6ef52

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_otpOf_final_seg
import Theorems.Thm_OrdinalStepUp_ErdosRado_otpOf_initial_lt

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution
    {𝒜 : Set _} (hA : IsIndec (otpOf wo 𝒜)) (hx : x ∈ 𝒜) :
    otpOf wo {y ∈ 𝒜 | ¬ wo.r y x} = otpOf wo 𝒜 := by
  refine otpOf_final_seg hA (fun _ hx => hx.1) ?_ ?_
  · exact fun _ ⟨hyB, hy⟩ _ hxA hyx ↦ ⟨hxA, hy ∘ (_root_.trans hyx)⟩
  · simp [otpOf_initial_lt hx]
end OrdinalStepUp.ErdosRado
