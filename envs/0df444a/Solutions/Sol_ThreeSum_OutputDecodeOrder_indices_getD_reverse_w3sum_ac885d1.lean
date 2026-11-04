-- Prove2me | solution 1 for ThreeSum.OutputDecodeOrder.indices_getD_reverse_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:34:47.516728+00:00
-- url     : https://prove2.me/submissions/f174c14e-598b-4a96-abc6-012b75b358e9

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Theorems.Thm_ThreeSum_OutputDecodeOrder_indices_length
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
theorem _root_.solution (m J k : ℕ) {j : ℕ} (hj : j < J) :
    (indices m J k).getD (J-1-j) 0 = (k/m^j)%m := by
  induction J generalizing k j with
  | zero => omega
  | succ J ih =>
    cases j with
    | zero =>
      have hlen := indices_length m J (k/m)
      simp only [indices,Nat.succ_eq_add_one,Nat.add_sub_cancel,Nat.sub_zero,pow_zero,Nat.div_one]
      rw [List.getD_append_right _ _ _ _ (by omega),hlen,Nat.sub_self]
      rfl
    | succ j =>
      have hj' : j < J := by omega
      have he : J+1-1-(j+1)=J-1-j := by omega
      simp only [indices,Nat.succ_eq_add_one]
      rw [he,List.getD_append _ _ _ _ (by rw [indices_length]; omega),ih (k/m) hj']
      rw [Nat.div_div_eq_div_mul,pow_succ']
end ThreeSum.OutputDecodeOrder
