-- Prove2me | solution 1 for PI.SqPairLocal.RU.cj_cj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:22:30.809531+00:00
-- url     : https://prove2.me/submissions/fe18d024-59b8-4b2f-a9d1-2f014c62b087

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_MemFixSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_ExistsConjugationFixedUniformizer
import Theorems.Thm_PI_SqPairLocal_RU_cj_coe

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
theorem _root_.solution (x : 𝓞 E) : cj E (cj E x) = x := by
  apply RingOfIntegers.ext
  rw [cj_coe, cj_coe, star_star]
end PI.SqPairLocal.RU
