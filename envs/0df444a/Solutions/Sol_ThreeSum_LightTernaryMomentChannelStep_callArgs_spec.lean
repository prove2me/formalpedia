-- Prove2me | solution 1 for ThreeSum.LightTernaryMomentChannelStep.callArgs_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:59:54.362185+00:00
-- url     : https://prove2.me/submissions/a65ea569-4dba-4369-97c9-fb598c5a6f86

import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannels
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentAccumulate
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannelStep
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



set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryMomentChannelStep
open Light TernaryWeightChannels
set_option maxHeartbeats 1500000
namespace ThreeSum.LightTernaryMomentChannelStep
theorem _root_.solution {lim : Limits} {loc μ : ℕ→ℤ} (positions : List ℕ) (vals : List ℤ)
    (hloc : ∀ i∈positions, loc i=frame vals i)
    (hword : ∀ i∈positions, |frame vals i|≤lim.word) :
    (∀ e∈callArgs positions, e.Safe lim ⟨loc,μ⟩) ∧
      (callArgs positions).map (·.val ⟨loc,μ⟩)=values positions vals := by
  constructor
  · intro e he
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
    simp only [v,Expr.Safe]
  · simp only [callArgs,values,List.map_map,Function.comp_def,v,Expr.val]
    exact List.map_congr_left hloc
end ThreeSum.LightTernaryMomentChannelStep
