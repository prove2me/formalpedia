-- Prove2me | solution 1 for ThreeSum.MaskDifference.subsetMask_union_sdiff_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:33:24.353977+00:00
-- url     : https://prove2.me/submissions/9345d794-4382-4b4b-8738-23464fbc7e52

import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_sum
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_empty
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero


attribute [local simp] ThreeSum.MaskDifference.subsetMask_empty

set_option autoImplicit false
open ThreeSum ThreeSum.MaskDifference
open Finset ThreeSum.SubsetAddress
namespace ThreeSum.MaskDifference
theorem _root_.solution {L : ℕ} (Q U : Finset (Fin L)) (hU : U ⊆ Q) :
    subsetMask U+subsetMask (Q \ U) = subsetMask Q := by
  have hd : Disjoint U (Q \ U) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.mem_sdiff.mp hb).2 ha
  have he : U ∪ (Q \ U) = Q := by
    ext a
    simp only [mem_union,mem_sdiff]
    constructor
    · rintro (ha | ⟨ha,_⟩)
      · exact hU ha
      · exact ha
    · intro ha
      by_cases hb : a ∈ U
      · exact Or.inl hb
      · exact Or.inr ⟨ha,hb⟩
  calc
    _ = (∑ i ∈ U, 2^i.val)+(∑ i ∈ Q \ U, 2^i.val) := by simp only [subsetMask_sum]
    _ = ∑ i ∈ U ∪ (Q \ U), 2^i.val := (Finset.sum_union hd).symm
    _ = subsetMask Q := by rw [he,subsetMask_sum]
end ThreeSum.MaskDifference
