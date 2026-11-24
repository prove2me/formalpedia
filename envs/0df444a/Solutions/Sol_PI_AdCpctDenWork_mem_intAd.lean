-- Prove2me | solution 1 for PI.AdCpctDenWork.mem_intAd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:38:45.187167+00:00
-- url     : https://prove2.me/submissions/8488a4df-f159-41f5-b6d1-17ecb8a6341e

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
theorem _root_.solution (a : FiniteAdeleRing (𝓞 F) F) :
    a ∈ intAd F ↔ ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F :=
  Iff.rfl
end PI.AdCpctDenWork
