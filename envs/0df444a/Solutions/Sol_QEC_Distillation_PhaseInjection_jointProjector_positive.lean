-- Prove2me | solution 1 for QEC.Distillation.PhaseInjection.jointProjector_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:09:55.379505+00:00
-- url     : https://prove2.me/submissions/728c5e25-d723-4fe4-8d5c-deaf2a1c3e7b

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Theorems.Thm_QEC_Distillation_PhaseInjection_jointProjector_eq_oneShotProjector

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseInjection
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open scoped TensorProduct
namespace QEC.Distillation.PhaseInjection
theorem _root_.solution :
    jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute positiveSyndrome =
      TwoQubit.zzEvenProjector := by
  calc
    jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute positiveSyndrome =
        oneShotProjector StabilizerOutcome.positive := by
          exact jointProjector_eq_oneShotProjector StabilizerOutcome.positive
    _ = TwoQubit.zzEvenProjector := oneShotProjector_positive
end QEC.Distillation.PhaseInjection
