-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.HostPrimeFacts.cj_inv_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:10.543798+00:00
-- url     : https://prove2.me/submissions/e46a72ef-e819-42f7-8cee-3cd63e91c094

import Definitions.Def_Formalism_PeriodIntegrals_EtaHostFacts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HostPrimeSplitting_FinrankOE
import Theorems.Thm_PI_UnitaryGroupMassFormula_HostPrimeFacts_cj_fix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host
open scoped Pointwise
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.HostPrimeFacts
variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)
namespace PI.UnitaryGroupMassFormula.HostPrimeFacts
theorem _root_.solution (a : 𝓞 H.F) :
    (cj H)⁻¹ • (algebraMap (𝓞 H.F) (𝓞 H.E) a) = algebraMap (𝓞 H.F) (𝓞 H.E) a := by
  conv_lhs => rw [← cj_fix H a]
  exact inv_smul_smul _ _
end PI.UnitaryGroupMassFormula.HostPrimeFacts
