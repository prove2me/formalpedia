-- Prove2me | solution 1 for QEC.Distillation.PhaseInjection.retryTwelveTargetHit_probability_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:24:59.439588+00:00
-- url     : https://prove2.me/submissions/d5af384c-c140-42ff-bfa3-cc1cd6b92a1b

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Theorems.Thm_QEC_Distillation_PhaseRetry_finiteCyclicRetry_twelve_target_hit_probability_one


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseInjection
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open scoped TensorProduct
namespace QEC.Distillation.PhaseInjection
theorem _root_.solution (start target : ZMod 12) :
    Filter.Tendsto (fun blocks =>
      PhaseRetry.targetHitProbability 12 blocks start target) Filter.atTop (nhds 1) :=
  PhaseRetry.finiteCyclicRetry_twelve_target_hit_probability_one start target
end QEC.Distillation.PhaseInjection
