-- Prove2me | solution 1 for QEC.Distillation.PhaseInjection.repeatedPhaseInjectionPhysicalTrace_ledger
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:40:55.817972+00:00
-- url     : https://prove2.me/submissions/adcec6bb-c01f-4394-8643-690d73894520

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseInjection
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open scoped TensorProduct
namespace QEC.Distillation.PhaseInjection
theorem _root_.solution (theta : Real) (coins : List Bool)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    (repeatedPhaseInjectionPhysicalTrace theta coins psi hpsi).2.1 =
      repeatedPhaseInjectionLedger theta coins psi hpsi := by
  induction coins generalizing psi with
  | nil => rfl
  | cons coin coins ih =>
      change {theta} +
        (repeatedPhaseInjectionPhysicalTrace theta coins
          (oneShotAttempt psi theta hpsi coin)
          (oneShotAttempt_norm psi theta hpsi coin)).2.1 = _
      rw [ih (oneShotAttempt psi theta hpsi coin)
        (oneShotAttempt_norm psi theta hpsi coin)]
      rfl
end QEC.Distillation.PhaseInjection
