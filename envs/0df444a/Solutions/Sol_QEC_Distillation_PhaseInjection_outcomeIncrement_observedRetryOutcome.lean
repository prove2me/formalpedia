-- Prove2me | solution 1 for QEC.Distillation.PhaseInjection.outcomeIncrement_observedRetryOutcome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:24:25.778479+00:00
-- url     : https://prove2.me/submissions/5f6cc914-a51d-4e15-8c1c-c7b067a59b18

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
theorem _root_.solution {q : Nat} (coin : Bool) :
    outcomeIncrement (q := q) (observedRetryOutcome coin) =
      PhaseRetry.signedIncrement (q := q) coin := by
  cases coin <;> rfl
end QEC.Distillation.PhaseInjection
