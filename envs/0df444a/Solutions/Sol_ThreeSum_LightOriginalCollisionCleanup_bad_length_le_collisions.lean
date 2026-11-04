-- Prove2me | solution 1 for ThreeSum.LightOriginalCollisionCleanup.bad_length_le_collisions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:47:12.62326+00:00
-- url     : https://prove2.me/submissions/4111e36a-7dbb-48c5-9705-40756ef59555

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
import Theorems.Thm_ThreeSum_TernaryOriginalCollisions_deleted_card_le_collisions
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
namespace ThreeSum.LightOriginalCollisionCleanup
theorem _root_.solution (keys : ℕ → ℕ) (n : ℕ) :
    (badIndices keys n).length≤
      (TernaryOriginalCollisions.collisionPairs (fun i : Fin n => keys i.val)).card := by
  let xs := badIndices keys n
  have hnodup : xs.Nodup := (List.nodup_range (n := n)).filter _
  have hxn : ∀ i∈xs, i<n := by
    intro i hi
    exact List.mem_range.mp (List.mem_filter.mp hi).1
  have hxdel : ∀ i (hi : i∈xs), (⟨i,hxn i hi⟩ : Fin n)∈
      TernaryOriginalCollisions.deleted (fun i : Fin n => keys i.val) := by
    intro i hi
    have hb : counts keys n (keys i)≠1 := by simpa using (List.mem_filter.mp hi).2
    obtain ⟨j,hj,hne,he⟩ := (count_self_ne_one_iff (hxn i hi)).mp hb
    simp only [TernaryOriginalCollisions.deleted,Finset.mem_filter,Finset.mem_univ,true_and]
    refine ⟨⟨j,hj⟩,?_,he.symm⟩
    intro hh
    exact hne (congrArg Fin.val hh).symm
  let f : (xs.toFinset) → (TernaryOriginalCollisions.deleted (fun i : Fin n => keys i.val)) :=
    fun a => ⟨⟨a.val,hxn a.val (List.mem_toFinset.mp a.property)⟩,
      hxdel a.val (List.mem_toFinset.mp a.property)⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun c => c.val.val) hab
  have hc := Fintype.card_le_of_injective f hinj
  have hlen : xs.toFinset.card=xs.length := List.toFinset_card_of_nodup hnodup
  have hb : xs.length≤(TernaryOriginalCollisions.deleted (fun i : Fin n => keys i.val)).card := by
    simpa only [Fintype.card_coe,hlen] using hc
  exact hb.trans (TernaryOriginalCollisions.deleted_card_le_collisions _)
end ThreeSum.LightOriginalCollisionCleanup
