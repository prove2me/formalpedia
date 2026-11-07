-- Prove2me | solution 1 for QEC.Distillation.PhaseRetry.targetMissProbability_le_certificate_twelve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:02:56.568055+00:00
-- url     : https://prove2.me/submissions/10c75bff-765a-476b-874d-f6b35a96aeda

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Theorems.Thm_QEC_Distillation_PhaseRetry_targetMissCard_le_certificate_twelve

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section
namespace QEC.Distillation.PhaseRetry
theorem _root_.solution (start target : ZMod 12) (blocks : Nat) :
    targetMissProbability 12 blocks start target ≤ certificateFailureProbability 12 blocks := by
  unfold targetMissProbability certificateFailureProbability
  apply div_le_div_of_nonneg_right
  · exact_mod_cast targetMissCard_le_certificate_twelve start target blocks
  · exact_mod_cast Nat.zero_le (Fintype.card (BlockTrace 12 blocks))
end QEC.Distillation.PhaseRetry
