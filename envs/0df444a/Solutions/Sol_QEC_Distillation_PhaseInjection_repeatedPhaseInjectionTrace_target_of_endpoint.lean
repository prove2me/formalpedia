-- Prove2me | solution 1 for QEC.Distillation.PhaseInjection.repeatedPhaseInjectionTrace_target_of_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:48:02.877489+00:00
-- url     : https://prove2.me/submissions/52414928-2d9a-4b82-824b-c17e2dc51c20

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Theorems.Thm_QEC_Distillation_PhaseInjection_repeatedPhaseInjectionTrace_output
import Theorems.Thm_QEC_Distillation_PhaseInjection_repeatedPhaseInjection_target_of_endpoint

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseInjection
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open scoped TensorProduct
namespace QEC.Distillation.PhaseInjection
theorem _root_.solution {q : Nat} [NeZero q]
    (coins : List Bool) (target : ZMod q) (psi : QubitSpace) (hpsi : ‖psi‖ = 1)
    (hendpoint : PhaseRetry.endpoint (0 : ZMod q) coins = target) :
    (repeatedPhaseInjectionTrace (phaseCycleAngle q) coins psi hpsi).1 =
      phaseInjectionHistoryGlobalPhase (phaseCycleAngle q) coins •
        phaseCycleTargetAction q target psi := by
  rw [repeatedPhaseInjectionTrace_output]
  exact repeatedPhaseInjection_target_of_endpoint coins target psi hpsi hendpoint
end QEC.Distillation.PhaseInjection
