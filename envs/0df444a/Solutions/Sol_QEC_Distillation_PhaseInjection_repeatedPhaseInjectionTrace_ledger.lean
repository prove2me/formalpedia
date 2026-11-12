-- Prove2me | solution 1 for QEC.Distillation.PhaseInjection.repeatedPhaseInjectionTrace_ledger
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:25:03.70422+00:00
-- url     : https://prove2.me/submissions/5b2e321b-4b1b-44bb-8294-1e49f33ca60d

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
    (repeatedPhaseInjectionTrace theta coins psi hpsi).2 =
      repeatedPhaseInjectionLedger theta coins psi hpsi :=
  rfl
end QEC.Distillation.PhaseInjection
