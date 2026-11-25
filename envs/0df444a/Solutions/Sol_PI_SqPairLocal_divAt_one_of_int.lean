-- Prove2me | solution 1 for PI.SqPairLocal.divAt_one_of_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:23:55.232452+00:00
-- url     : https://prove2.me/submissions/e996412f-55db-4e84-8d28-e41df5271788

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_DivAtOneOfInt

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
variable {E : Type} [Field E] [NumberField E] [StarRing E]
variable {Q : Ideal (𝓞 E)} [hQ : Q.IsPrime]
namespace PI.SqPairLocal
theorem _root_.solution {x : E} (hx : IntAt Q x) : DivAt Q 1 x := by
  unfold IntAt at hx
  unfold DivAt
  obtain ⟨s, hs, w, hw⟩ := hx
  exact ⟨s, hs, w, by simp [hw]⟩
end PI.SqPairLocal
