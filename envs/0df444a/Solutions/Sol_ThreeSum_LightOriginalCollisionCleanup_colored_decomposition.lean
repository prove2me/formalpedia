-- Prove2me | solution 1 for ThreeSum.LightOriginalCollisionCleanup.colored_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:58:01.522268+00:00
-- url     : https://prove2.me/submissions/bf6fcae7-6c83-473f-a7ed-e72416627135

import Definitions.Def_Submission_ThreeSum_LightDeletedTwoSum
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionCleanup
import Theorems.Thm_ThreeSum_LightOriginalCollisionCleanup_count_self_ne_one_iff
import Theorems.Thm_ThreeSum_LightOriginalCollisionCleanup_hit_iff
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LightColoredTwoSum_flag_zero
import Theorems.Thm_ThreeSum_LightDeletedTwoSum_flag_zero
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightOriginalBucketFilter_bad_zero
import Theorems.Thm_ThreeSum_LightOriginalBucketFilter_good_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LightColoredTwoSum.flag_zero
attribute [local simp] ThreeSum.LightDeletedTwoSum.flag_zero
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightOriginalBucketFilter.bad_zero
attribute [local simp] ThreeSum.LightOriginalBucketFilter.good_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalCollisionCleanup
open Light ThreeSum.LightSubsetAddress
open ThreeSum.LightOriginalBucketFilter
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightOriginalCollisionCleanup
theorem _root_.solution (A B C : ℕ → ℤ) (keysB keysC : ℕ → ℕ) (nA nB nC : ℕ) :
    (∃ i<nA, ∃ j<nB, ∃ k<nC, C k=A i+B j) ↔
      LightDeletedTwoSum.Hit (badIndex keysB nB) B A C nC nA (badIndices keysB nB).length 1 ∨
      LightDeletedTwoSum.Hit (badIndex keysC nC) C A B nB nA (badIndices keysC nC).length (-1) ∨
      ∃ i<nA, ∃ j∈good keysB (counts keysB nB) nB, ∃ k∈good keysC (counts keysC nC) nC,
        C k=A i+B j := by
  rw [hit_iff,hit_iff]
  constructor
  · rintro ⟨i,hi,j,hj,k,hk,he⟩
    by_cases hb : counts keysB nB (keysB j)=1
    · by_cases hc : counts keysC nC (keysC k)=1
      · apply Or.inr
        apply Or.inr
        refine ⟨i,hi,j,?_,k,?_,he⟩
        · exact List.mem_filter.mpr ⟨List.mem_range.mpr hj,by simpa using hb⟩
        · exact List.mem_filter.mpr ⟨List.mem_range.mpr hk,by simpa using hc⟩
      · apply Or.inr
        apply Or.inl
        refine ⟨k,hk,(count_self_ne_one_iff hk).mp hc,i,hi,j,hj,?_⟩
        omega
    · apply Or.inl
      refine ⟨j,hj,(count_self_ne_one_iff hj).mp hb,i,hi,k,hk,?_⟩
      simpa using he
  · rintro (⟨j,hj,_,i,hi,k,hk,he⟩ | ⟨k,hk,_,i,hi,j,hj,he⟩ | ⟨i,hi,j,hj,k,hk,he⟩)
    · exact ⟨i,hi,j,hj,k,hk,by simpa using he⟩
    · exact ⟨i,hi,j,hj,k,hk,by omega⟩
    · exact ⟨i,hi,j,List.mem_range.mp (List.mem_filter.mp hj).1,
        k,List.mem_range.mp (List.mem_filter.mp hk).1,he⟩
end ThreeSum.LightOriginalCollisionCleanup
