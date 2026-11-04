-- Prove2me | solution 1 for ThreeSum.LightBoxStages.time_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:49:23.54932+00:00
-- url     : https://prove2.me/submissions/fd7c59e6-02d0-4b83-8be7-6366154ba947

import Definitions.Def_Submission_ThreeSum_LightZetaPass
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_BoxStages
import Definitions.Def_Submission_ThreeSum_LightBoxStages
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_BoxStages_mem_prefix
import Theorems.Thm_ThreeSum_BoxStages_prefix_all
import Theorems.Thm_ThreeSum_BoxStages_prefix_zero
import Theorems.Thm_ThreeSum_BoxStages_stageValue_all
import Theorems.Thm_ThreeSum_BoxStages_stageValue_zero
import Theorems.Thm_ThreeSum_LightDownsetSize_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound
import Theorems.Thm_ThreeSum_LightZetaBatch_time_bound
import Theorems.Thm_ThreeSum_LightZetaCell_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_223d9caf4e7f660b
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_SubsetStages_mem_suffix
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_all
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_zero
import Theorems.Thm_ThreeSum_SubsetStages_suffix_all
import Theorems.Thm_ThreeSum_SubsetStages_suffix_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.BoxStages.mem_prefix
attribute [local simp] ThreeSum.BoxStages.prefix_all
attribute [local simp] ThreeSum.BoxStages.prefix_zero
attribute [local simp] ThreeSum.BoxStages.stageValue_all
attribute [local simp] ThreeSum.BoxStages.stageValue_zero
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.SubsetStages.mem_suffix
attribute [local simp] ThreeSum.SubsetStages.stageValue_all
attribute [local simp] ThreeSum.SubsetStages.stageValue_zero
attribute [local simp] ThreeSum.SubsetStages.suffix_all
attribute [local simp] ThreeSum.SubsetStages.suffix_zero



set_option autoImplicit false
open ThreeSum ThreeSum.LightBoxStages
open Light ThreeSum.SubsetAddress ThreeSum.BoxStages ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBoxStages
theorem _root_.solution {L cut : ℕ} (hcut : cut ≤ L) :
    time L cut ≤ 6000*(L+1)^4*(downsetCap L cut+1) := by
  have hc := LightZetaPass.time_bound hcut
  have hs := LightDownsetSize.time_bound L
  have hmul := Nat.mul_le_mul_left L hc
  have hpow₂ : (L+1)^2 ≤ (L+1)^4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hpow₄ : 1 ≤ (L+1)^4 := Nat.one_le_pow' 4 L
  have hlarge : (L+1)^4 ≤ (L+1)^4*(downsetCap L cut+1) := by
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hlin : L+1 ≤ (L+1)^4 := by
    have hh := Nat.pow_le_pow_right (show 1 ≤ L+1 by omega) (show 1 ≤ 4 by omega)
    simpa using hh
  have hlarge : (L+1)*((L+1)^3*(downsetCap L cut+1)) = (L+1)^4*(downsetCap L cut+1) := by ring
  have htrans : L*(4000*(L+1)^3*(downsetCap L cut+1)) ≤
      4000*((L+1)^4*(downsetCap L cut+1)) := by
    have hh := Nat.mul_le_mul_right (4000*(L+1)^3*(downsetCap L cut+1))
      (show L ≤ L+1 by omega)
    nlinarith [hlarge]
  unfold time
  nlinarith
end ThreeSum.LightBoxStages
