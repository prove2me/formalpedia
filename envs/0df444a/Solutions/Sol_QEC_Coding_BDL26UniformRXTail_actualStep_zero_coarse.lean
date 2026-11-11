-- Prove2me | solution 1 for QEC.Coding.BDL26UniformRXTail.actualStep_zero_coarse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:47:00.868241+00:00
-- url     : https://prove2.me/submissions/71626868-9e60-449f-b9f0-d6564b8e3de1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_StoppedReadout
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxStepOutput_weight
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_rzStepOutput_weight


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26UniformRXTail
theorem _root_.solution (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (sigma : (indexedFamily S depth).Syndrome i.succ) (hs : sigma.val = 0) :
    (actualStep S depth i sigma).coarse.val = 0 := by
  apply (HammingWeight_eq_zero_iff _).mp
  by_cases h : i.val % 2 = 0
  · rw [actualStep_rx S depth i h]
    have hw := BDL26RXDecoderAdapter.rxStepOutput_weight S depth i h sigma
    rw [hs, HammingWeight_zero] at hw
    omega
  · rw [actualStep_rz S depth i h]
    have hw := BDL26RZDecoderAdapter.rzStepOutput_weight S depth i h sigma
    rw [hs, HammingWeight_zero] at hw
    exact Nat.eq_zero_of_le_zero hw
end QEC.Coding.BDL26UniformRXTail
