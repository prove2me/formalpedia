-- Prove2me | solution 1 for QEC.Distillation.PhaseInjection.phaseEightTargetAction_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:38:24.00734+00:00
-- url     : https://prove2.me/submissions/1dfbd830-8ee6-4fa9-a5b8-979f3288cd56

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Theorems.Thm_QEC_Distillation_PhaseInjection_phaseCycleAngle_eight

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseInjection
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open scoped TensorProduct
namespace QEC.Distillation.PhaseInjection
theorem _root_.solution (target : ZMod 8) :
    phaseEightTargetAction target =
      OneQubitMagic.phaseShiftOperator ((-Real.pi / 4) * target.val) := by
  rw [phaseEightTargetAction, phaseCycleTargetAction, phaseCycleAngle_eight]
end QEC.Distillation.PhaseInjection
