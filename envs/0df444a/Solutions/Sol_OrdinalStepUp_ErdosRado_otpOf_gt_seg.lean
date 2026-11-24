-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.otpOf_gt_seg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:50:55.408991+00:00
-- url     : https://prove2.me/submissions/3b755b82-1ef6-4352-8dce-aca107233a62

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_otpOf_final_seg
import Theorems.Thm_OrdinalStepUp_ErdosRado_otpOf_final_seg_at
import Theorems.Thm_OrdinalStepUp_ErdosRado_otpOf_singleton

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution
    {𝒜 : Set _} (hA : IsIndec (otpOf wo 𝒜))
    {v : wo.α} (hv : v ∈ 𝒜) : otpOf wo {x ∈ 𝒜 | wo.r v x} = otpOf wo 𝒜 := by
  have hcut := otpOf_final_seg_at hA hv
  refine Eq.trans (otpOf_final_seg (𝒜 := {x ∈ 𝒜 | ¬ wo.r x v}) (hcut ▸ hA)
    (fun _ hx => ⟨hx.1, asymm hx.2⟩) (fun _ hy _ hx hyx => ⟨hx.1, _root_.trans hy.2 hyx⟩) ?_) hcut
  have hdiff : {x ∈ 𝒜 | ¬ wo.r x v} \ {x ∈ 𝒜 | wo.r v x} = {v} := by
    ext
    grind only [irrefl_of wo.r, trichotomous_of wo.r, Set.mem_sdiff, Set.mem_ofPred_eq,
      Set.mem_singleton_iff]
  rw [hdiff, otpOf_singleton, hcut]
  exact hA.one_lt
end OrdinalStepUp.ErdosRado
