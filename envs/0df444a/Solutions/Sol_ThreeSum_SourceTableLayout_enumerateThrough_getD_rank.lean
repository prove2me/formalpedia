-- Prove2me | solution 1 for ThreeSum.SourceTableLayout.enumerateThrough_getD_rank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:05:00.266449+00:00
-- url     : https://prove2.me/submissions/5fa7c410-829c-476a-b97e-55a32a80f848

import Definitions.Def_Submission_ThreeSum_LightZetaCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Mathlib.Data.List.GetD
import Definitions.Def_Submission_ThreeSum_SourceTableLayout
import Theorems.Thm_ThreeSum_SourceTableLayout_enumerateLayer_getD_rank
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_SubsetAddress_enumerateThrough_length
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_mono
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_succ
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
theorem _root_.solution {L k m cut : ℕ} (hm : IsMask L k m)
    (hk : k ≤ cut) (fallback : ℕ) :
    (enumerateThrough L cut).getD (downsetRank L m) fallback = m := by
  induction cut with
  | zero =>
      have hk0 : k=0 := by omega
      subst k
      simpa only [enumerateThrough,downsetRank,hm.2,layerOffset_zero,zero_add] using
        enumerateLayer_getD_rank hm fallback
  | succ cut ih =>
      rw [enumerateThrough]
      by_cases hlow : k ≤ cut
      · rw [List.getD_append _ _ _ _ (by
          rw [enumerateThrough_length]
          have hlt := layerRank_lt hm
          have hle := layerOffset_mono L (Nat.succ_le_succ hlow)
          simp only [Nat.succ_eq_add_one] at hle
          rw [layerOffset_succ L k] at hle
          unfold downsetRank
          rw [hm.2]
          omega)]
        exact ih hlow
      · have he : k=cut+1 := by omega
        subst k
        rw [downsetRank,hm.2]
        rw [List.getD_append_right _ _ _ _ (by
          rw [enumerateThrough_length]
          omega),enumerateThrough_length,Nat.add_sub_cancel_left]
        exact enumerateLayer_getD_rank hm fallback
end ThreeSum.SourceTableLayout
