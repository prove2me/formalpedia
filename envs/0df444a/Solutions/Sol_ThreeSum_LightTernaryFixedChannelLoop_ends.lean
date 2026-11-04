-- Prove2me | solution 1 for ThreeSum.LightTernaryFixedChannelLoop.ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:47:06.578661+00:00
-- url     : https://prove2.me/submissions/2d7d9c15-9a7e-4d86-bdb8-fe4784f70f1e

import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannelStep
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
import Definitions.Def_Submission_ThreeSum_LightTernaryFixedChannelLoop
import Theorems.Thm_ThreeSum_LightTernaryFixedChannelLoop_arguments_spec
import Theorems.Thm_ThreeSum_LightTernaryFixedChannelLoop_arguments_cost
import Theorems.Thm_Light_Ends_callThen
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
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
theorem _root_.solution (steps : List Channel) (entry : Channel→ℕ) (cost : Channel→ℕ)
    (vals : List ℤ) (loc μ : ℕ→ℤ) (I : ℕ→(ℕ→ℤ)→Prop)
    (hd : d<lim.depth) (hloc : ∀ i<vals.length, loc i=frame vals i)
    (hI : I 0 μ)
    (hstep : ∀ i<steps.length, ∀ ν, I i ν →
      Meets lim P (entry (steps.getD i (0,0))) (d+1) vals ν
        (cost (steps.getD i (0,0))) (fun _ ξ => I (i+1) ξ)) :
    Ends lim P d (body steps entry vals.length) ⟨loc,μ⟩
      (time steps cost vals.length) (fun σ => I steps.length σ.mem) := by
  induction steps generalizing loc μ I with
  | nil => exact Ends.skip hI
  | cons c cs ih =>
    have hc := hstep 0 (by simp) μ hI
    simp only [List.getD_cons_zero] at hc
    unfold body time
    refine Ends.callThen hc ?_ (ha := arguments_spec vals hloc) (hd := hd)
      (hT := by rw [arguments_cost]; omega)
    intro r ν hν
    have hloc' : ∀ i<vals.length, Function.update loc vals.length r i=frame vals i := by
      intro i hi
      rw [Function.update_of_ne (by omega)]
      exact hloc i hi
    have htail : ∀ i<cs.length, ∀ ξ, I (i+1) ξ →
        Meets lim P (entry (cs.getD i (0,0))) (d+1) vals ξ
          (cost (cs.getD i (0,0))) (fun _ ζ => I (i+1+1) ζ) := by
      intro i hi ξ hξ
      have hh := hstep (i+1) (by simp; omega) ξ hξ
      simpa only [List.getD_cons_succ] using hh
    have hh := ih (Function.update loc vals.length r) ν (fun i => I (i+1)) hloc' hν htail
    have ht : time cs cost vals.length≤
        vals.length+2+cost c+time cs cost vals.length-
          (((arguments vals.length).map Expr.cost).sum+2+cost c) := by
      rw [arguments_cost]
      omega
    apply hh.mono ht
    intro σ hσ
    simpa only [List.length_cons] using hσ
end ThreeSum.LightTernaryFixedChannelLoop
