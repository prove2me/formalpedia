-- Prove2me | solution 1 for QEC.Distillation.HH18PhaseInjection.tInvOutcomeCorrection_favorable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:33:34.858339+00:00
-- url     : https://prove2.me/submissions/6ae8f236-97ce-4174-b7d0-78703680fd55

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
    tInvOutcomeCorrection true = 1 :=
  rfl
end QEC.Distillation.HH18PhaseInjection
