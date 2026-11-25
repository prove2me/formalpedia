-- Prove2me | solution 1 for PI.SqPairLocal.ne_bot_of_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:22:30.524302+00:00
-- url     : https://prove2.me/submissions/24245989-72d3-44de-ac91-ed6b7ed138db

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsMaximalComapCj

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
theorem _root_.solution {Q : Ideal (𝓞 E)} (hQ : Q.IsMaximal) : Q ≠ ⊥ := by
  first
    | exact Ring.ne_bot_of_isMaximal_of_not_isField hQ (RingOfIntegers.not_isField E)
    | exact Ring.ne_bot_of_isMaximal_of_not_isField hQ (NumberField.RingOfIntegers.not_isField E)
end PI.SqPairLocal
