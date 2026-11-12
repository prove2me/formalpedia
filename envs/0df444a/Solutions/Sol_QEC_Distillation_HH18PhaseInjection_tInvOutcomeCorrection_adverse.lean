-- Prove2me | solution 1 for QEC.Distillation.HH18PhaseInjection.tInvOutcomeCorrection_adverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:33:26.903822+00:00
-- url     : https://prove2.me/submissions/0c8a9cb7-91e6-4125-9a5a-293ef9f9fad7

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18PhaseInjection
open Semantics Semantics.Qubit
namespace QEC.Distillation.HH18PhaseInjection
theorem _root_.solution :
    tInvOutcomeCorrection false =
      OneQubitMagic.phaseShiftOperator (-Real.pi / 2) :=
  rfl
end QEC.Distillation.HH18PhaseInjection
