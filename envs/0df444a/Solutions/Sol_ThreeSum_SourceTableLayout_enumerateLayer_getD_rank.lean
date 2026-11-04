-- Prove2me | solution 1 for ThreeSum.SourceTableLayout.enumerateLayer_getD_rank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:59:29.974508+00:00
-- url     : https://prove2.me/submissions/baf7125d-c204-4d9c-9db5-871a1628aec5

import Definitions.Def_Submission_ThreeSum_LightZetaCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Mathlib.Data.List.GetD
import Definitions.Def_Submission_ThreeSum_SourceTableLayout
import Theorems.Thm_ThreeSum_SourceTableLayout_layerRank_zero
import Theorems.Thm_ThreeSum_SourceTableLayout_getD_map_of_lt
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_List_getD_map_of_lt
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_le_width
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low
import Theorems.Thm_ThreeSum_SubsetAddress_enumerateLayer_length
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Definitions.Def_WeightedCache3SUM_Alias_a5ea34939403d75f
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.SourceTableLayout
open SubsetAddress
set_option maxHeartbeats 800000
namespace ThreeSum.SourceTableLayout
theorem _root_.solution {L k m : ℕ} (hm : IsMask L k m) (fallback : ℕ) :
    (enumerateLayer L k).getD (layerRank L k m) fallback = m := by
  induction L generalizing k m fallback with
  | zero =>
      have hk := hm.le_width
      have hb := hm.1
      have hk0 : k=0 := by omega
      have hm0 : m=0 := by simp only [pow_zero] at hb; omega
      subst k; subst m
      simp [enumerateLayer,layerRank]
  | succ L ih =>
      cases k with
      | zero =>
          have hm0 := (isMask_zero (L+1) m).mp hm
          subst m
          simp [enumerateLayer,layerRank_zero]
      | succ k =>
          rw [enumerateLayer,if_pos hm.le_width]
          by_cases hc : m < 2^L
          · rw [layerRank,if_pos hc]
            rw [List.getD_append _ _ _ _ (by
              rw [enumerateLayer_length]
              exact layerRank_lt (hm.low hc))]
            exact ih (hm.low hc) fallback
          · have hh := (hm.high (Nat.le_of_not_gt hc)).2
            simp only [Nat.add_sub_cancel] at hh
            rw [layerRank,if_neg hc]
            simp only [Nat.add_sub_cancel]
            rw [List.getD_append_right _ _ _ _ (by
              rw [enumerateLayer_length]
              omega),enumerateLayer_length,Nat.add_sub_cancel_left]
            rw [getD_map_of_lt _ _ 0 _ (by
              rw [enumerateLayer_length]
              exact layerRank_lt hh),ih hh 0]
            omega
end ThreeSum.SourceTableLayout
