-- Prove2me | solution 1 for ThreeSum.TernaryStoredSpan.represents_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:58:07.096045+00:00
-- url     : https://prove2.me/submissions/a91e8972-d6ba-4359-a43c-7874a39d6412

import Definitions.Def_Submission_ThreeSum_LightSpanCatalogTest
import Definitions.Def_Submission_ThreeSum_TernaryStoredSpan
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryStoredSpan
open ThreeSum
set_option maxHeartbeats 3000000
variable {p J n : ℕ}
namespace ThreeSum.TernaryStoredSpan
theorem _root_.solution : Represents (p := p) (J := J) (fun _ _ => 0) 1 [] := by
  intro w
  have he : {v | v∈([] : List (Fin J → ZMod p))}=(∅ : Set (Fin J → ZMod p)) := by ext v; simp
  rw [he,Submodule.span_empty,Submodule.mem_bot]
  constructor
  · intro h
    subst w
    exact ⟨0,by decide,by intro i; simp⟩
  · rintro ⟨k,hk,he⟩
    exact funext (fun i => by simpa using (he i).symm)
end ThreeSum.TernaryStoredSpan
