-- Prove2me | solution 1 for QEC.Distillation.PhaseRetry.targetMissProbability_twelve_tends_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:04:09.460983+00:00
-- url     : https://prove2.me/submissions/06fc81cb-71c3-4713-8b17-67d7f9e3156b

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Theorems.Thm_QEC_Distillation_PhaseRetry_certificateFailureProbability_twelve
import Theorems.Thm_QEC_Distillation_PhaseRetry_targetMissProbability_le_certificate_twelve
import Theorems.Thm_QEC_Distillation_PhaseRetry_almostSureTargetHit_of_le_certificateTail
import Theorems.Thm_QEC_Distillation_PhaseRetry_certificateFailureTail_twelve_tends_zero

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section
namespace QEC.Distillation.PhaseRetry
theorem _root_.solution (start target : ZMod 12) :
    AlmostSureTargetHit (fun blocks => targetMissProbability 12 blocks start target) := by
  apply almostSureTargetHit_of_le_certificateTail
  · intro blocks
    unfold targetMissProbability
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro blocks
    calc
      targetMissProbability 12 blocks start target ≤ certificateFailureProbability 12 blocks :=
        targetMissProbability_le_certificate_twelve start target blocks
      _ = certificateFailureTail 12 blocks := by
        simp only [certificateFailureProbability_twelve, certificateFailureTail]
        norm_num
  · exact certificateFailureTail_twelve_tends_zero
end QEC.Distillation.PhaseRetry
