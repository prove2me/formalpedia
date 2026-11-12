-- Prove2me | solution 1 for QEC.Distillation.PhaseInjection.phaseTwelveTargetAction_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:38:50.090797+00:00
-- url     : https://prove2.me/submissions/4ec59ae2-7f3e-4453-8f06-f11e3e7e6682

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Theorems.Thm_QEC_Distillation_PhaseInjection_phaseCycleAngle_twelve

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseInjection
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open scoped TensorProduct
namespace QEC.Distillation.PhaseInjection
theorem _root_.solution (target : ZMod 12) :
    phaseTwelveTargetAction target =
      OneQubitMagic.phaseShiftOperator ((-Real.pi / 6) * target.val) := by
  rw [phaseTwelveTargetAction, phaseCycleTargetAction, phaseCycleAngle_twelve]
end QEC.Distillation.PhaseInjection
