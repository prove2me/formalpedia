-- Prove2me | solution 1 for QEC.Distillation.PhaseInjection.phaseInjectionStoppingLedger_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:51:21.122285+00:00
-- url     : https://prove2.me/submissions/d3aa0256-5a2e-4ecd-9b4f-904abccfc75b

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Theorems.Thm_QEC_Distillation_PhaseInjection_repeatedPhaseInjectionLedger_eq_replicate
import Theorems.Thm_QEC_Distillation_PhaseInjection_repeatedPhaseInjectionPhysicalTrace_ledger
import Theorems.Thm_QEC_Distillation_PhaseInjection_retryTraceCoins_length
import Theorems.Thm_QEC_Distillation_PhaseInjection_stoppingHistory_length_le

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseInjection
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open scoped TensorProduct
namespace QEC.Distillation.PhaseInjection
theorem _root_.solution {q blocks : Nat}
    (start target : ZMod q) (trace : PhaseRetry.BlockTrace q blocks)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    ∃ attempts ≤ q * blocks,
      phaseInjectionStoppingLedger start target trace psi hpsi =
        Multiset.replicate attempts (phaseCycleAngle q) := by
  refine ⟨(stoppingHistory start target (retryTraceCoins blocks trace)).length, ?_, ?_⟩
  · calc
      (stoppingHistory start target (retryTraceCoins blocks trace)).length ≤
          (retryTraceCoins blocks trace).length :=
        stoppingHistory_length_le start target (retryTraceCoins blocks trace)
      _ = q * blocks := retryTraceCoins_length trace
  · unfold phaseInjectionStoppingLedger phaseInjectionStoppingTrace
    rw [repeatedPhaseInjectionPhysicalTrace_ledger,
      repeatedPhaseInjectionLedger_eq_replicate]
end QEC.Distillation.PhaseInjection
