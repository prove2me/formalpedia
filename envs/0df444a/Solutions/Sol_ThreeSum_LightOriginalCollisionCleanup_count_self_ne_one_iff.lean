-- Prove2me | solution 1 for ThreeSum.LightOriginalCollisionCleanup.count_self_ne_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:44:50.965582+00:00
-- url     : https://prove2.me/submissions/63b60f3e-0803-40a7-83b5-27ecec69da4c

import Definitions.Def_Submission_ThreeSum_LightDeletedTwoSum
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionCleanup
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
namespace ThreeSum.LightOriginalCollisionCleanup
theorem _root_.solution {keys : ℕ → ℕ} {n i : ℕ} (hi : i<n) :
    counts keys n (keys i)≠1 ↔ ∃ j<n, j≠i ∧ keys j=keys i := by
  have hm : i∈(Finset.range n).filter (fun j => keys j=keys i) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,rfl⟩
  change ((Finset.range n).filter (fun j => keys j=keys i)).card≠1 ↔ _
  constructor
  · intro h
    by_contra hn
    have he : (Finset.range n).filter (fun j => keys j=keys i)={i} := by
      ext j
      constructor
      · intro hj
        obtain ⟨hjn,he⟩ := Finset.mem_filter.mp hj
        have hji : j=i := by
          by_contra hne
          exact hn ⟨j,Finset.mem_range.mp hjn,hne,he⟩
        simp [hji]
      · intro hj
        simpa only [Finset.mem_singleton.mp hj] using hm
    exact h (by rw [he]; simp)
  · rintro ⟨j,hj,hne,he⟩ hcard
    obtain ⟨k,hk⟩ := Finset.card_eq_one.mp hcard
    have hiK : i=k := Finset.mem_singleton.mp (hk ▸ hm)
    have hjM : j∈(Finset.range n).filter (fun j => keys j=keys i) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,he⟩
    have hjK : j=k := Finset.mem_singleton.mp (hk ▸ hjM)
    exact hne (hjK.trans hiK.symm)
end ThreeSum.LightOriginalCollisionCleanup
