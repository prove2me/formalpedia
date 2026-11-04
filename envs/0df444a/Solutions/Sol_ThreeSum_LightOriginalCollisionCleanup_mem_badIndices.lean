-- Prove2me | solution 1 for ThreeSum.LightOriginalCollisionCleanup.mem_badIndices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:49:09.92592+00:00
-- url     : https://prove2.me/submissions/beb04011-6aaf-446c-9088-94a9e78caeca

import Definitions.Def_Submission_ThreeSum_LightDeletedTwoSum
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionCleanup
import Theorems.Thm_ThreeSum_LightOriginalCollisionCleanup_count_self_ne_one_iff
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
theorem _root_.solution {keys : ℕ → ℕ} {n i : ℕ} :
    i∈badIndices keys n ↔ i<n ∧ ∃ j<n, j≠i ∧ keys j=keys i := by
  constructor
  · intro hi
    obtain ⟨hin,hcount⟩ := List.mem_filter.mp hi
    have hin' : i<n := List.mem_range.mp hin
    exact ⟨hin',(count_self_ne_one_iff hin').mp (of_decide_eq_true hcount)⟩
  · rintro ⟨hin,hpartner⟩
    exact List.mem_filter.mpr ⟨List.mem_range.mpr hin,by
      simpa using (count_self_ne_one_iff hin).mpr hpartner⟩
end ThreeSum.LightOriginalCollisionCleanup
