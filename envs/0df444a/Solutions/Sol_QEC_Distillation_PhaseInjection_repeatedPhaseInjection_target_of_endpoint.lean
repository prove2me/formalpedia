-- Prove2me | solution 1 for QEC.Distillation.PhaseInjection.repeatedPhaseInjection_target_of_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:45:37.578611+00:00
-- url     : https://prove2.me/submissions/681c2800-c0d3-4d93-a98a-8b2fd8f10d61

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Theorems.Thm_QEC_Distillation_PhaseInjection_repeatedPhaseInjection_action
import Theorems.Thm_QEC_Distillation_PhaseInjection_phaseCycleTargetAction_of_endpoint

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
    repeatedPhaseInjection (phaseCycleAngle q) coins psi hpsi =
      phaseInjectionHistoryGlobalPhase (phaseCycleAngle q) coins •
        phaseCycleTargetAction q target psi := by
  rw [repeatedPhaseInjection_action,
    phaseCycleTargetAction_of_endpoint coins target hendpoint]
end QEC.Distillation.PhaseInjection
