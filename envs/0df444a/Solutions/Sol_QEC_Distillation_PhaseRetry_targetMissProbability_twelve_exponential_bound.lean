-- Prove2me | solution 1 for QEC.Distillation.PhaseRetry.targetMissProbability_twelve_exponential_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:20:13.904204+00:00
-- url     : https://prove2.me/submissions/4108c4b2-c451-4eb0-ab4d-d77f416c93b0

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Theorems.Thm_QEC_Distillation_PhaseRetry_certificateFailureProbability_twelve
import Theorems.Thm_QEC_Distillation_PhaseRetry_targetMissProbability_le_certificate_twelve

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section
namespace QEC.Distillation.PhaseRetry
theorem _root_.solution
    (start target : ZMod 12) (blocks : Nat) :
    targetMissProbability 12 blocks start target ≤ (4095 / 4096 : Real) ^ blocks := by
  calc
    targetMissProbability 12 blocks start target ≤ certificateFailureProbability 12 blocks :=
      targetMissProbability_le_certificate_twelve start target blocks
    _ = (4095 / 4096 : Real) ^ blocks := certificateFailureProbability_twelve blocks
end QEC.Distillation.PhaseRetry
