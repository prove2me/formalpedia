-- Prove2me | solution 1 for QEC.Distillation.PhaseRetry.certificateFailureProbability_eight_tends_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:20:16.786633+00:00
-- url     : https://prove2.me/submissions/f3fd88b3-53ac-4474-a6ea-e54924facbb2

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Theorems.Thm_QEC_Distillation_PhaseRetry_certificateFailureProbability_eight

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section
namespace QEC.Distillation.PhaseRetry
theorem _root_.solution :
    AlmostSureTargetHit (certificateFailureProbability 8) := by
  unfold AlmostSureTargetHit
  have h : certificateFailureProbability 8 = fun blocks => (255 / 256 : Real) ^ blocks := by
    funext blocks
    exact certificateFailureProbability_eight blocks
  rw [h]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : Real) ≤ 255 / 256)
    (by norm_num : (255 / 256 : Real) < 1)
end QEC.Distillation.PhaseRetry
