-- Prove2me | solution 1 for ThreeSum.SubsetStages.stageValue_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:57:44.883324+00:00
-- url     : https://prove2.me/submissions/b17e1eea-d9b4-459c-a27a-b8c5d5ffda23

import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_SubsetStages
import Theorems.Thm_ThreeSum_SubsetStages_mem_suffix
import Theorems.Thm_ThreeSum_SubsetStages_suffix_zero
import Theorems.Thm_ThreeSum_SubsetStages_suffix_all
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_Subset_partialZeta_empty
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero


attribute [local simp] ThreeSum.SubsetStages.mem_suffix
attribute [local simp] ThreeSum.SubsetStages.suffix_zero
attribute [local simp] ThreeSum.SubsetStages.suffix_all

set_option autoImplicit false
open ThreeSum ThreeSum.SubsetStages
open Finset
namespace ThreeSum.SubsetStages
theorem _root_.solution {L : ℕ} (f : Finset (Fin L) → ℤ) : stageValue f 0 = f := by
  funext S
  simp [stageValue,Subset.partialZeta_empty]
end ThreeSum.SubsetStages
