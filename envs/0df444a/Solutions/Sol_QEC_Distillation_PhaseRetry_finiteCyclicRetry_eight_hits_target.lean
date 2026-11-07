-- Prove2me | solution 1 for QEC.Distillation.PhaseRetry.finiteCyclicRetry_eight_hits_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:20:02.011683+00:00
-- url     : https://prove2.me/submissions/72824698-d427-4dda-8f3e-67ec5961a19b

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Theorems.Thm_QEC_Distillation_PhaseRetry_positiveBlock_suffix_visits_target_eight

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section
namespace QEC.Distillation.PhaseRetry
theorem _root_.solution (start target : ZMod 8) :
    FiniteCyclicRetryHitsTarget 8 start target := by
  intro history
  exact positiveBlock_suffix_visits_target_eight start target history
end QEC.Distillation.PhaseRetry
