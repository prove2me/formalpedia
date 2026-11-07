-- Prove2me | solution 1 for QEC.Distillation.PhaseRetry.finiteCyclicRetry_twelve_target_hit_probability_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:20:27.42399+00:00
-- url     : https://prove2.me/submissions/676e7b94-f173-4a80-9a45-3f3b6d294373

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Theorems.Thm_QEC_Distillation_PhaseRetry_targetMissProbability_twelve_tends_zero

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section
namespace QEC.Distillation.PhaseRetry
theorem _root_.solution (start target : ZMod 12) :
    Filter.Tendsto (fun blocks => targetHitProbability 12 blocks start target)
      Filter.atTop (nhds 1) := by
  unfold targetHitProbability
  have h := targetMissProbability_twelve_tends_zero start target
  unfold AlmostSureTargetHit at h
  simpa using
    ((tendsto_const_nhds : Filter.Tendsto (fun _ : Nat => (1 : Real)) Filter.atTop (nhds 1)).sub h)
end QEC.Distillation.PhaseRetry
