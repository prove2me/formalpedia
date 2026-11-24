-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.exists_wo_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:51:30.440858+00:00
-- url     : https://prove2.me/submissions/0b55a287-2492-4eef-8c10-26ae64d74e48

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_otpOf_gt_seg
import Theorems.Thm_OrdinalStepUp_ErdosRado_nonempty_of_otpOf_eq

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution
    {𝒜 : Set _} (hA : IsIndec (otpOf wo 𝒜))
    {v : _} (hv : v ∈ 𝒜) : ∃ w ∈ 𝒜, wo.r v w := by
  -- the part of `𝒜` strictly above `v` still has type `otpOf wo 𝒜`, so it is
  -- nonempty; any of its points is above `v`.
  have : IsIndec (otpOf wo {x ∈ 𝒜 | wo.r v x}) := by
    rw [otpOf_gt_seg hA hv]; exact hA
  obtain ⟨w, hw⟩ := nonempty_of_otpOf_eq this
  exact ⟨w, hw.1, hw.2⟩
end OrdinalStepUp.ErdosRado
