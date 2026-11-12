-- Prove2me | solution 1 for QEC.Distillation.HH18PhaseInjection.idealTInvResourceUse_resource
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:42:15.198578+00:00
-- url     : https://prove2.me/submissions/f047ffdd-bbc3-47ee-ac4d-9eea6cff756e

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection
import Theorems.Thm_QEC_Distillation_HH18NoisyInput_tInvResourceErrorDensity_zero_eq_phaseStateDensity


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18PhaseInjection
open Semantics Semantics.Qubit
namespace QEC.Distillation.HH18PhaseInjection
theorem _root_.solution :
    (PhaseInjection.phaseStateResourceUse tInvIdealAngle).resource =
      HH18NoisyInput.tInvResourceErrorDensity 0 := by
  change OneQubitMagic.phaseStateDensity tInvIdealAngle =
    HH18NoisyInput.tInvResourceErrorDensity 0
  rw [HH18NoisyInput.tInvResourceErrorDensity_zero_eq_phaseStateDensity]
  rfl
end QEC.Distillation.HH18PhaseInjection
