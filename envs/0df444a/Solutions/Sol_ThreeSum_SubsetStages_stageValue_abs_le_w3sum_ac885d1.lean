-- Prove2me | solution 1 for ThreeSum.SubsetStages.stageValue_abs_le_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:40:09.53835+00:00
-- url     : https://prove2.me/submissions/453f0b69-ccc2-4980-843c-0e6bcaefa43e

import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_SubsetStages
import Theorems.Thm_ThreeSum_SubsetStages_mem_suffix
import Theorems.Thm_ThreeSum_SubsetStages_suffix_zero
import Theorems.Thm_ThreeSum_SubsetStages_suffix_all
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_zero
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_succ
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_all
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_Subset_zetaStep_stays_in_downset
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero


attribute [local simp] ThreeSum.SubsetStages.mem_suffix
attribute [local simp] ThreeSum.SubsetStages.suffix_zero
attribute [local simp] ThreeSum.SubsetStages.suffix_all
attribute [local simp] ThreeSum.SubsetStages.stageValue_zero
attribute [local simp] ThreeSum.SubsetStages.stageValue_all

set_option autoImplicit false
open ThreeSum ThreeSum.SubsetStages
open Finset
namespace ThreeSum.SubsetStages
theorem _root_.solution {L cut U : ℕ} (f : Finset (Fin L) → ℤ)
    (hf : ∀ S, S.card ≤ cut → |f S| ≤ U) :
    ∀ j ≤ L, ∀ S, S.card ≤ cut → |stageValue f j S| ≤ ((2^j*U : ℕ) : ℤ) := by
  intro j
  induction j with
  | zero =>
    intro hj S hS
    simpa only [stageValue_zero,pow_zero,one_mul] using hf S hS
  | succ j ih =>
    intro hj S hS
    have hjL : j < L := by omega
    have h₁ := ih (by omega) S hS
    have h₂ := ih (by omega) (S.erase (nextCoord j hjL))
      (Subset.zetaStep_stays_in_downset S (nextCoord j hjL) cut hS)
    have hdouble : ((2^(j+1)*U : ℕ) : ℤ) =
        ((2^j*U : ℕ) : ℤ)+((2^j*U : ℕ) : ℤ) := by
      push_cast
      rw [pow_succ]
      ring
    rw [stageValue_succ f hjL,Subset.zetaStep,hdouble]
    split
    · exact (abs_add_le _ _).trans (add_le_add h₁ h₂)
    · exact h₁.trans (by have hnonneg : (0 : ℤ) ≤ ((2^j*U : ℕ) : ℤ) := Int.natCast_nonneg _; omega)
end ThreeSum.SubsetStages
