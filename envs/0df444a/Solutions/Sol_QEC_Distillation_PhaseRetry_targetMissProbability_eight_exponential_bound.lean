-- Prove2me | solution 1 for QEC.Distillation.PhaseRetry.targetMissProbability_eight_exponential_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:20:10.955569+00:00
-- url     : https://prove2.me/submissions/a775a453-a259-497b-8415-32b88aa50280

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Theorems.Thm_QEC_Distillation_PhaseRetry_certificateFailureProbability_eight
import Theorems.Thm_QEC_Distillation_PhaseRetry_targetMissProbability_le_certificate_eight

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section
namespace QEC.Distillation.PhaseRetry
theorem _root_.solution
    (start target : ZMod 8) (blocks : Nat) :
    targetMissProbability 8 blocks start target ≤ (255 / 256 : Real) ^ blocks := by
  calc
    targetMissProbability 8 blocks start target ≤ certificateFailureProbability 8 blocks :=
      targetMissProbability_le_certificate_eight start target blocks
    _ = (255 / 256 : Real) ^ blocks := certificateFailureProbability_eight blocks
end QEC.Distillation.PhaseRetry
