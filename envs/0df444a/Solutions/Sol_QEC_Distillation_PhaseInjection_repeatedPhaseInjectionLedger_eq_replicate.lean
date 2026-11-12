-- Prove2me | solution 1 for QEC.Distillation.PhaseInjection.repeatedPhaseInjectionLedger_eq_replicate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:37:27.809374+00:00
-- url     : https://prove2.me/submissions/f9be24ca-d8a5-4368-848d-524329ff7693

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
    repeatedPhaseInjectionLedger theta coins psi hpsi =
      Multiset.replicate coins.length theta := by
  induction coins generalizing psi with
  | nil => rfl
  | cons coin coins ih =>
      change {theta} + repeatedPhaseInjectionLedger theta coins
        (oneShotAttempt psi theta hpsi coin)
        (oneShotAttempt_norm psi theta hpsi coin) =
          Multiset.replicate (coins.length + 1) theta
      rw [ih (oneShotAttempt psi theta hpsi coin)
        (oneShotAttempt_norm psi theta hpsi coin), Multiset.replicate_succ]
      rfl
end QEC.Distillation.PhaseInjection
