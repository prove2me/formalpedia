-- Prove2me | solution 1 for QEC.Distillation.PhaseRetry.targetMissProbability_le_certificate_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:02:44.92225+00:00
-- url     : https://prove2.me/submissions/689fac7f-ae69-4628-ab1a-c71740273f87

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Theorems.Thm_QEC_Distillation_PhaseRetry_targetMissCard_le_certificate_eight

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section
namespace QEC.Distillation.PhaseRetry
theorem _root_.solution (start target : ZMod 8) (blocks : Nat) :
    targetMissProbability 8 blocks start target ≤ certificateFailureProbability 8 blocks := by
  unfold targetMissProbability certificateFailureProbability
  apply div_le_div_of_nonneg_right
  · exact_mod_cast targetMissCard_le_certificate_eight start target blocks
  · exact_mod_cast Nat.zero_le (Fintype.card (BlockTrace 8 blocks))
end QEC.Distillation.PhaseRetry
