-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.HostPrimeFacts.finrank_OE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:40:22.622479+00:00
-- url     : https://prove2.me/submissions/862e4b2a-7d3c-4eae-8bf0-c04a98c68547

import Definitions.Def_Formalism_PeriodIntegrals_EtaHostFacts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HostPrimeSplitting_FinrankOE
import Theorems.Thm_Formalism_FrobeniusOrbits_isCMField_hostE
import Theorems.Thm_Formalism_HC_HostAx_isCMField_hostE


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
theorem _root_.solution : Module.finrank (𝓞 H.F) (𝓞 H.E) = 2 := by
  haveI := H.isCMField_hostE
  rw [← IsFractionRing.finrank_eq (𝓞 H.F) H.F (𝓞 H.E) H.E]
  exact Algebra.IsQuadraticExtension.finrank_eq_two _ _
end PI.UnitaryGroupMassFormula.HostPrimeFacts
