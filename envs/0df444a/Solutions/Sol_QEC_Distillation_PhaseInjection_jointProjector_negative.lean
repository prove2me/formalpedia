-- Prove2me | solution 1 for QEC.Distillation.PhaseInjection.jointProjector_negative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:10:50.568644+00:00
-- url     : https://prove2.me/submissions/909405fd-e694-4229-b2f8-ebc52b3831d2

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
    jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute negativeSyndrome =
      TwoQubit.zzOddProjector := by
  calc
    jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute negativeSyndrome =
        oneShotProjector StabilizerOutcome.negative := by
          exact jointProjector_eq_oneShotProjector StabilizerOutcome.negative
    _ = TwoQubit.zzOddProjector := oneShotProjector_negative
end QEC.Distillation.PhaseInjection
