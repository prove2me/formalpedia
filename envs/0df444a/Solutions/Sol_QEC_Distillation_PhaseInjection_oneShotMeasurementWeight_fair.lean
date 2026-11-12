-- Prove2me | solution 1 for QEC.Distillation.PhaseInjection.oneShotMeasurementWeight_fair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:39:38.463383+00:00
-- url     : https://prove2.me/submissions/17be6eb4-f94b-4378-80fb-7102128d9336

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Theorems.Thm_QEC_Distillation_PhaseInjection_oneShotProjectedWeight_fair
import Theorems.Thm_QEC_Distillation_PhaseInjection_oneShotMeasurementWeight_eq_projector_norm_sq

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseInjection
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open scoped TensorProduct
namespace QEC.Distillation.PhaseInjection
theorem _root_.solution (psi : QubitSpace) (theta : Real)
    (hpsi : ‖psi‖ = 1) (coin : Bool) :
    oneShotMeasurementWeight psi theta hpsi coin = (1 / 2 : Real) := by
  rw [oneShotMeasurementWeight_eq_projector_norm_sq]
  exact oneShotProjectedWeight_fair psi theta hpsi coin
end QEC.Distillation.PhaseInjection
