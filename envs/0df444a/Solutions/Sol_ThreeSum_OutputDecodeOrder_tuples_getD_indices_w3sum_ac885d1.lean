-- Prove2me | solution 1 for ThreeSum.OutputDecodeOrder.tuples_getD_indices_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:39:12.254918+00:00
-- url     : https://prove2.me/submissions/7ea5b016-b91a-457c-ac9c-8f98b71e5762

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Theorems.Thm_ThreeSum_OutputDecodeOrder_getD_flatMap_uniform
import Theorems.Thm_ThreeSum_OutputDecodeOrder_tuples_succ_right
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_List_getD_map_of_lt
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_RadixKeyLists_tuples_length
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
theorem _root_.solution (base : List α) (da : α) (hm : 0 < base.length)
    (J k : ℕ) (hk : k < base.length^J) :
    (tuples base J).getD k [] = (indices base.length J k).map (fun i => base.getD i da) := by
  induction J generalizing k with
  | zero =>
    have hk0 : k=0 := by simpa using hk
    subst k
    rfl
  | succ J ih =>
    have hq : k/base.length < base.length^J :=
      (Nat.div_lt_iff_lt_mul hm).mpr (by simpa only [pow_succ] using hk)
    have hr : k%base.length < base.length := Nat.mod_lt _ hm
    have hi : k/base.length < (tuples base J).length := by rwa [tuples_length]
    have hidx : k/base.length*base.length+k%base.length=k := by
      simpa only [Nat.mul_comm] using Nat.div_add_mod k base.length
    conv_lhs => rw [tuples_succ_right,← hidx]
    rw [getD_flatMap_uniform _ _ base.length (by simp) [] [] hi hr]
    rw [List.getD_map_of_lt _ hr da []]
    rw [ih _ hq]
    simp only [indices,List.map_append,List.map_cons,List.map_nil]
end ThreeSum.OutputDecodeOrder
