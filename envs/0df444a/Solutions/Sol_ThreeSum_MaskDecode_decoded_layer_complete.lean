-- Prove2me | solution 1 for ThreeSum.MaskDecode.decoded_layer_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:16:37.914349+00:00
-- url     : https://prove2.me/submissions/68175de8-4749-45f2-a4b3-f51a62ac980e

import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Theorems.Thm_ThreeSum_MaskDecode_decode_subsetMask
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_mem_enumerateLayer
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_isMask
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.MaskDecode
open Finset
open scoped BigOperators
open SubsetAddress
namespace ThreeSum.MaskDecode
theorem _root_.solution {L k : ℕ} (s : Finset (Fin L)) (hs : s.card = k) :
    s ∈ (enumerateLayer L k).map (decode L) := by
  apply List.mem_map.mpr
  refine ⟨subsetMask s, (mem_enumerateLayer L k _).mpr ?_, decode_subsetMask s⟩
  simpa only [hs] using subsetMask_isMask s
end ThreeSum.MaskDecode
