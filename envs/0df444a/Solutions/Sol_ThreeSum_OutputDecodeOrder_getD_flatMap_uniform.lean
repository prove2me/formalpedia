-- Prove2me | solution 1 for ThreeSum.OutputDecodeOrder.getD_flatMap_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:15:41.889069+00:00
-- url     : https://prove2.me/submissions/5288cde8-dcb3-4a5a-a324-3536f93ae6dd

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
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
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeOrder
open RadixKeyLists
set_option maxHeartbeats 1800000
set_option maxRecDepth 6000
variable {α β : Type*}
namespace ThreeSum.OutputDecodeOrder
theorem _root_.solution (xs : List α) (f : α → List β) (q : ℕ)
    (hf : ∀ x ∈ xs, (f x).length=q) (da : α) (db : β)
    {z r : ℕ} (hz : z < xs.length) (hr : r < q) :
    (xs.flatMap f).getD (z*q+r) db = (f (xs.getD z da)).getD r db := by
  induction xs generalizing z with
  | nil => simp at hz
  | cons x xs ih =>
    have hlen : (f x).length=q := hf x (by simp)
    have htail : ∀ a ∈ xs, (f a).length=q := fun a ha => hf a (by simp [ha])
    cases z with
    | zero =>
      simp only [Nat.zero_mul,Nat.zero_add,List.getD_cons_zero,List.flatMap_cons]
      exact List.getD_append _ _ _ _ (by omega)
    | succ z =>
      have hz' : z < xs.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hz
      have hoff : (z+1)*q+r-q=z*q+r := by simp only [Nat.add_mul,one_mul]; omega
      rw [List.flatMap_cons,List.getD_append_right _ _ _ _ (by
        rw [hlen]
        simp only [Nat.succ_eq_add_one,Nat.add_mul,one_mul]
        omega),hlen]
      rw [hoff,List.getD_cons_succ]
      exact ih htail hz'
end ThreeSum.OutputDecodeOrder
