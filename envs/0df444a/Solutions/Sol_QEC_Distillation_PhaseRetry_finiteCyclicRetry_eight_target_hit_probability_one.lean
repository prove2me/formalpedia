-- Prove2me | solution 1 for QEC.Distillation.PhaseRetry.finiteCyclicRetry_eight_target_hit_probability_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:20:22.701961+00:00
-- url     : https://prove2.me/submissions/4304ac02-81c8-4bd5-a338-f95fb28c2ea2

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Theorems.Thm_QEC_Distillation_PhaseRetry_targetMissProbability_eight_tends_zero

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section
namespace QEC.Distillation.PhaseRetry
theorem _root_.solution (start target : ZMod 8) :
    Filter.Tendsto (fun blocks => targetHitProbability 8 blocks start target)
      Filter.atTop (nhds 1) := by
  unfold targetHitProbability
  have h := targetMissProbability_eight_tends_zero start target
  unfold AlmostSureTargetHit at h
  simpa using
    ((tendsto_const_nhds : Filter.Tendsto (fun _ : Nat => (1 : Real)) Filter.atTop (nhds 1)).sub h)
end QEC.Distillation.PhaseRetry
