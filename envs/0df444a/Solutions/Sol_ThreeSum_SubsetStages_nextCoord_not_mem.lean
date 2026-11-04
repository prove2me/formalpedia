-- Prove2me | solution 1 for ThreeSum.SubsetStages.nextCoord_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:13:12.042822+00:00
-- url     : https://prove2.me/submissions/ffbfd1a5-d5bd-421c-a776-23d7105a929f

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
theorem _root_.solution {L j : ℕ} (hj : j < L) : nextCoord j hj ∉ suffix L j := by
  simp only [mem_suffix,nextCoord]
  omega
end ThreeSum.SubsetStages
