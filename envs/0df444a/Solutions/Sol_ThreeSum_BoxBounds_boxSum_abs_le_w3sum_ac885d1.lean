-- Prove2me | solution 1 for ThreeSum.BoxBounds.boxSum_abs_le_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:36:10.891836+00:00
-- url     : https://prove2.me/submissions/dab84b5b-41cc-4755-89cb-85dd60dfbddb

import Definitions.Def_Submission_ThreeSum_BoxStages
import Definitions.Def_Submission_ThreeSum_BoxBounds
import Theorems.Thm_ThreeSum_BoxStages_mem_prefix
import Theorems.Thm_ThreeSum_BoxStages_prefix_all
import Theorems.Thm_ThreeSum_BoxStages_prefix_zero
import Theorems.Thm_ThreeSum_BoxStages_stageValue_all
import Theorems.Thm_ThreeSum_BoxStages_stageValue_zero
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_le_width
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_isMask
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_SubsetStages_mem_suffix
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_all
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_zero
import Theorems.Thm_ThreeSum_SubsetStages_suffix_all
import Theorems.Thm_ThreeSum_SubsetStages_suffix_zero
attribute [local simp] ThreeSum.BoxStages.mem_prefix
attribute [local simp] ThreeSum.BoxStages.prefix_all
attribute [local simp] ThreeSum.BoxStages.prefix_zero
attribute [local simp] ThreeSum.BoxStages.stageValue_all
attribute [local simp] ThreeSum.BoxStages.stageValue_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.SubsetStages.mem_suffix
attribute [local simp] ThreeSum.SubsetStages.stageValue_all
attribute [local simp] ThreeSum.SubsetStages.stageValue_zero
attribute [local simp] ThreeSum.SubsetStages.suffix_all
attribute [local simp] ThreeSum.SubsetStages.suffix_zero



set_option autoImplicit false
open ThreeSum ThreeSum.BoxBounds
open Finset ThreeSum.SubsetAddress
namespace ThreeSum.BoxBounds
theorem _root_.solution {L cut U : ℕ} (flags free : Finset (Fin L))
    (weight : Finset (Fin L) → ℤ) (hflags : flags.card ≤ cut)
    (hweight : ∀ S, S.card ≤ cut → |weight S| ≤ U) :
    |SparseBoxes.boxSum flags free weight| ≤ ((2^L*U : ℕ) : ℤ) := by
  have hwidth := (subsetMask_isMask flags).le_width
  have hpow := Nat.pow_le_pow_right (show 1 ≤ (2 : ℕ) by decide) hwidth
  have hmul := Nat.mul_le_mul_right U hpow
  unfold SparseBoxes.boxSum
  calc
    _ ≤ ∑ leaf ∈ flags.powerset, |if flags \ free ⊆ leaf then weight leaf else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _leaf ∈ flags.powerset, (U : ℤ) := by
      apply Finset.sum_le_sum
      intro leaf hl
      have hcard := (Finset.card_le_card (Finset.mem_powerset.mp hl)).trans hflags
      split
      · exact hweight leaf hcard
      · simp
    _ = ((2^flags.card*U : ℕ) : ℤ) := by simp
    _ ≤ _ := by exact_mod_cast hmul
end ThreeSum.BoxBounds
