-- Prove2me | solution 1 for ThreeSum.SubsetStages.mem_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:52:09.503165+00:00
-- url     : https://prove2.me/submissions/95500605-6e9a-4b0c-9695-76c1748095ad

import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_SubsetStages
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.SubsetStages
open Finset
namespace ThreeSum.SubsetStages
theorem _root_.solution {L j : ℕ} (a : Fin L) : a ∈ suffix L j ↔ L-j ≤ a.val := by
  simp [suffix]
end ThreeSum.SubsetStages
