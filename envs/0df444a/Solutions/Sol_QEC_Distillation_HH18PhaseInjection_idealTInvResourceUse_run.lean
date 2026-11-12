-- Prove2me | solution 1 for QEC.Distillation.HH18PhaseInjection.idealTInvResourceUse_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:28:11.895599+00:00
-- url     : https://prove2.me/submissions/45665a5c-adf6-4541-b03b-362184db60a9

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection
import Theorems.Thm_QEC_Distillation_PhaseInjection_phaseStateResourceUse_run_eq_injectionInputDensity


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18PhaseInjection
open Semantics Semantics.Qubit
namespace QEC.Distillation.HH18PhaseInjection
theorem _root_.solution (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    (PhaseInjection.phaseStateResourceUse tInvIdealAngle).run
        (PhaseInjection.sourceInputDensity psi hpsi) =
      PhaseInjection.injectionInputDensity psi tInvIdealAngle hpsi := by
  exact PhaseInjection.phaseStateResourceUse_run_eq_injectionInputDensity
    psi tInvIdealAngle hpsi
end QEC.Distillation.HH18PhaseInjection
