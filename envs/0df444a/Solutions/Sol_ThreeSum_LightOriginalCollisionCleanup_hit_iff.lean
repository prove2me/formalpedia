-- Prove2me | solution 1 for ThreeSum.LightOriginalCollisionCleanup.hit_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:53:13.509447+00:00
-- url     : https://prove2.me/submissions/8bbba2ff-4a91-4c55-9e60-a7df0fc87eba

import Definitions.Def_Submission_ThreeSum_LightDeletedTwoSum
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionCleanup
import Theorems.Thm_ThreeSum_LightOriginalCollisionCleanup_mem_badIndices
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
theorem _root_.solution {keys : ℕ → ℕ} {n scanN targetN : ℕ}
    (values scan target : ℕ → ℤ) (sign : ℤ) :
    LightDeletedTwoSum.Hit (badIndex keys n) values scan target targetN scanN (badIndices keys n).length sign ↔
      ∃ i<n, (∃ j<n, j≠i ∧ keys j=keys i) ∧ LightColoredTwoSum.Hit scan target targetN scanN (values i) sign := by
  constructor
  · rintro ⟨j,hj,hh⟩
    have hm : badIndex keys n j∈badIndices keys n := by
      simpa only [badIndex,dif_pos hj] using List.getElem_mem hj
    obtain ⟨hin,hpartner⟩ := mem_badIndices.mp hm
    exact ⟨_,hin,hpartner,hh⟩
  · rintro ⟨i,hin,hpartner,hh⟩
    have hm : i∈badIndices keys n := mem_badIndices.mpr ⟨hin,hpartner⟩
    obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hm
    refine ⟨j,hj,?_⟩
    simpa only [badIndex,dif_pos hj,he] using hh
end ThreeSum.LightOriginalCollisionCleanup
