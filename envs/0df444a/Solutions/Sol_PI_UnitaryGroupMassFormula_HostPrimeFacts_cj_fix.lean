-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.HostPrimeFacts.cj_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:33:54.859542+00:00
-- url     : https://prove2.me/submissions/e4002c6c-6cab-4845-9a5c-375431929e5e

import Definitions.Def_Formalism_PeriodIntegrals_EtaHostFacts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HostPrimeSplitting_FinrankOE
import Theorems.Thm_Formalism_FrobeniusOrbits_conjE_mem_hostF_iff
import Theorems.Thm_Formalism_HC_HostAx_conjE_mem_hostF_iff


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
    (cj H) • (algebraMap (𝓞 H.F) (𝓞 H.E) a) = algebraMap (𝓞 H.F) (𝓞 H.E) a := by
  apply RingOfIntegers.coe_injective
  show (cj H) ((algebraMap (𝓞 H.F) (𝓞 H.E) a : 𝓞 H.E) : H.E) = _
  have hc : ((algebraMap (𝓞 H.F) (𝓞 H.E) a : 𝓞 H.E) : H.E) = (((a : H.F)) : H.E) := rfl
  rw [hc]
  exact (H.conjE_mem_hostF_iff _).mp (a : H.F).2
end PI.UnitaryGroupMassFormula.HostPrimeFacts
