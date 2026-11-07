-- Prove2me | solution 1 for QEC.Distillation.PhaseRetry.targetMissProbability_eight_tends_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:04:08.326132+00:00
-- url     : https://prove2.me/submissions/08a5d643-43ad-4760-ad3c-7af6a60450b2

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Theorems.Thm_QEC_Distillation_PhaseRetry_certificateFailureProbability_eight
import Theorems.Thm_QEC_Distillation_PhaseRetry_targetMissProbability_le_certificate_eight
import Theorems.Thm_QEC_Distillation_PhaseRetry_almostSureTargetHit_of_le_certificateTail
import Theorems.Thm_QEC_Distillation_PhaseRetry_certificateFailureTail_eight_tends_zero

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section
namespace QEC.Distillation.PhaseRetry
theorem _root_.solution (start target : ZMod 8) :
    AlmostSureTargetHit (fun blocks => targetMissProbability 8 blocks start target) := by
  apply almostSureTargetHit_of_le_certificateTail
  · intro blocks
    unfold targetMissProbability
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro blocks
    calc
      targetMissProbability 8 blocks start target ≤ certificateFailureProbability 8 blocks :=
        targetMissProbability_le_certificate_eight start target blocks
      _ = certificateFailureTail 8 blocks := by
        simp only [certificateFailureProbability_eight, certificateFailureTail]
        norm_num
  · exact certificateFailureTail_eight_tends_zero
end QEC.Distillation.PhaseRetry
