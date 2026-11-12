-- Prove2me | solution 1 for QEC.Distillation.HH18PhaseInjection.erroredTInvResourceUse_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:28:15.529984+00:00
-- url     : https://prove2.me/submissions/70337acb-9fb8-4865-8fb5-19782a07e605

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
    (PhaseInjection.phaseStateResourceUse tInvErrorAngle).run
        (PhaseInjection.sourceInputDensity psi hpsi) =
      PhaseInjection.injectionInputDensity psi tInvErrorAngle hpsi := by
  exact PhaseInjection.phaseStateResourceUse_run_eq_injectionInputDensity
    psi tInvErrorAngle hpsi
end QEC.Distillation.HH18PhaseInjection
