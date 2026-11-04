-- Prove2me | solution 1 for ThreeSum.TernaryMomentSchedule.channel_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:47:24.754819+00:00
-- url     : https://prove2.me/submissions/a9fe9129-954c-4cef-a564-306dc6d836f4

import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
import Theorems.Thm_ThreeSum_TernaryMomentSchedule_aggregate_nil
import Theorems.Thm_ThreeSum_TernaryMomentSchedule_aggregate_cons
import Theorems.Thm_ThreeSum_TernaryMomentSchedule_aggregate_append
import Theorems.Thm_ThreeSum_TernaryMomentSchedule_aggregate_row
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_total_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryWeightChannels_leftMoment_eval
import Theorems.Thm_ThreeSum_TernaryWeightChannels_powerCircuit_eval
import Theorems.Thm_ThreeSum_TernaryWeightChannels_rightMoment_eval
import Theorems.Thm_ThreeSum_TernaryWeightChannels_scalarPower_eval
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightTernaryWeightedHistogram.total_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryWeightChannels.leftMoment_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.powerCircuit_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.rightMoment_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.scalarPower_eval


attribute [local simp] ThreeSum.TernaryMomentSchedule.aggregate_nil
attribute [local simp] ThreeSum.TernaryMomentSchedule.aggregate_cons
attribute [local simp] ThreeSum.TernaryMomentSchedule.aggregate_append

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryMomentSchedule
open Finset TernaryJointType
open scoped BigOperators
namespace ThreeSum.TernaryMomentSchedule
theorem _root_.solution (terms k i : ℕ) (score : ℕ→ℕ→ℕ→ℤ) :
    aggregate (channels terms) score k i=
      if k<terms then ∑ j∈range (k+1), score k j i else 0 := by
  classical
  induction terms with
  | zero => simp [channels]
  | succ t ih =>
    rw [channels,aggregate_append,ih,aggregate_row]
    by_cases hkt : k<t
    · have hne : t≠k := by omega
      simp [hkt,hne,show k<t+1 by omega]
    · by_cases hke : k=t
      · subst k; simp
      · have hne : t≠k := by omega
        simp [hkt,hne,show ¬k<t+1 by omega]
end ThreeSum.TernaryMomentSchedule
