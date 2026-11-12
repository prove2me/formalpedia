-- Prove2me | solution 1 for QEC.Distillation.HH18PhaseInjection.erroredTInvResourceUse_resource
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:37:06.217201+00:00
-- url     : https://prove2.me/submissions/faf980a3-99b9-4942-8573-37d0f342aefd

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection
import Theorems.Thm_QEC_Distillation_HH18PhaseInjection_tInvErrorResourceDensity_eq_phaseStateDensity
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18PhaseInjection
open Semantics Semantics.Qubit
namespace QEC.Distillation.HH18PhaseInjection
theorem _root_.solution :
    (PhaseInjection.phaseStateResourceUse tInvErrorAngle).resource =
      HH18NoisyInput.tInvResourceErrorDensity 1 := by
  change OneQubitMagic.phaseStateDensity tInvErrorAngle =
    HH18NoisyInput.tInvResourceErrorDensity 1
  exact tInvErrorResourceDensity_eq_phaseStateDensity.symm
end QEC.Distillation.HH18PhaseInjection
