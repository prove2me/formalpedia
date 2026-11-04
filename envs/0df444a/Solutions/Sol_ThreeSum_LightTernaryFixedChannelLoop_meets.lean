-- Prove2me | solution 1 for ThreeSum.LightTernaryFixedChannelLoop.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:51:29.234493+00:00
-- url     : https://prove2.me/submissions/3d723c30-3360-4a53-aa1d-067bbeb4c1a6

import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannelStep
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
import Definitions.Def_Submission_ThreeSum_LightTernaryFixedChannelLoop
import Theorems.Thm_ThreeSum_LightTernaryFixedChannelLoop_arguments_cost
import Theorems.Thm_ThreeSum_LightTernaryFixedChannelLoop_ends
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightTernaryMomentChannelStep_callArgs_cost
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_total_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryMomentSchedule_aggregate_append
import Theorems.Thm_ThreeSum_TernaryMomentSchedule_aggregate_cons
import Theorems.Thm_ThreeSum_TernaryMomentSchedule_aggregate_nil
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
attribute [local simp] ThreeSum.LightTernaryMomentChannelStep.callArgs_cost
attribute [local simp] ThreeSum.LightTernaryWeightedHistogram.total_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryMomentSchedule.aggregate_append
attribute [local simp] ThreeSum.TernaryMomentSchedule.aggregate_cons
attribute [local simp] ThreeSum.TernaryMomentSchedule.aggregate_nil
attribute [local simp] ThreeSum.TernaryWeightChannels.leftMoment_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.powerCircuit_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.rightMoment_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.scalarPower_eval


attribute [local simp] ThreeSum.LightTernaryFixedChannelLoop.arguments_cost

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFixedChannelLoop
open Light
set_option maxHeartbeats 1500000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryFixedChannelLoop
theorem _root_.solution {steps : List Channel} {entry cost : Channel→ℕ} {vals : List ℤ}
    {pMain : ℕ} (hmain : P[pMain]?=some (body steps entry vals.length))
    (μ : ℕ→ℤ) (I : ℕ→(ℕ→ℤ)→Prop) (hd : d<lim.depth) (hI : I 0 μ)
    (hstep : ∀ i<steps.length, ∀ ν, I i ν →
      Meets lim P (entry (steps.getD i (0,0))) (d+1) vals ν
        (cost (steps.getD i (0,0))) (fun _ ξ => I (i+1) ξ)) :
    Meets lim P pMain d vals μ (time steps cost vals.length)
      (fun _ ν => I steps.length ν) := by
  exact Meets.of_body hmain (ends steps entry cost vals (frame vals) μ I hd (by simp) hI hstep)
end ThreeSum.LightTernaryFixedChannelLoop
