-- Prove2me | solution 1 for PI.AdCpctDenWork.natCast_mem_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:45.018403+00:00
-- url     : https://prove2.me/submissions/2b6a0bf8-7504-4d73-a94a-616ef740a0fc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdCpctDen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicCompactDensity_ExistsNatLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.AdCpctDenWork
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {F : Type} [Field F] [NumberField F]
namespace PI.AdCpctDenWork
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    (n : v.adicCompletion F) ∈ v.adicCompletionIntegers F :=
  natCast_mem _ n
end PI.AdCpctDenWork
