-- Prove2me | solution 1 for PI.SqPairLocal.cj_cj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:46:06.144422+00:00
-- url     : https://prove2.me/submissions/d3493549-1509-4d4e-b5ed-b7d89eba0343

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsMaximalComapCj
import Theorems.Thm_PI_SqPairLocal_coe_cj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
namespace PI.SqPairLocal
theorem _root_.solution (x : 𝓞 E) : cj E (cj E x) = x := by
  have h : ((cj E (cj E x) : 𝓞 E) : E) = (x : E) := by rw [coe_cj, coe_cj, star_star]
  first
    | exact_mod_cast h
    | exact RingOfIntegers.ext h
    | exact Subtype.ext h
end PI.SqPairLocal
