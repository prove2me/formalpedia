-- Prove2me | solution 1 for PI.SqPairLocal.RU.cj_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:47:16.518679+00:00
-- url     : https://prove2.me/submissions/c91282ee-a85b-4117-a826-83000f8c9c0e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_MemFixSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_ExistsConjugationFixedUniformizer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.SqPairLocal PI.SqPairLocal.RU
variable {E : Type} [Field E] [NumberField E] [StarRing E]
namespace PI.SqPairLocal.RU
theorem _root_.solution (x : 𝓞 E) : ((cj E x : 𝓞 E) : E) = star (x : E) := rfl
end PI.SqPairLocal.RU
