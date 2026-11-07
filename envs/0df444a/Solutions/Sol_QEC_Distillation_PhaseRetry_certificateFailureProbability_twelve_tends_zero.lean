-- Prove2me | solution 1 for QEC.Distillation.PhaseRetry.certificateFailureProbability_twelve_tends_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:20:21.546889+00:00
-- url     : https://prove2.me/submissions/b0f4d137-8ca4-4b21-be16-77419342add7

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Theorems.Thm_QEC_Distillation_PhaseRetry_certificateFailureProbability_twelve

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section
namespace QEC.Distillation.PhaseRetry
theorem _root_.solution :
    AlmostSureTargetHit (certificateFailureProbability 12) := by
  unfold AlmostSureTargetHit
  have h : certificateFailureProbability 12 = fun blocks => (4095 / 4096 : Real) ^ blocks := by
    funext blocks
    exact certificateFailureProbability_twelve blocks
  rw [h]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : Real) ≤ 4095 / 4096)
    (by norm_num : (4095 / 4096 : Real) < 1)
end QEC.Distillation.PhaseRetry
