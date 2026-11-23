-- Prove2me | solution 1 for PI.AdCpctDenWork.natCast_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:45.047185+00:00
-- url     : https://prove2.me/submissions/066bd37a-c3c6-40a1-b438-e377ba73378d

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
theorem _root_.solution (n : ℕ) (a : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    ((n : FiniteAdeleRing (𝓞 F) F) * a) v = (n : v.adicCompletion F) * a v :=
  rfl
end PI.AdCpctDenWork
