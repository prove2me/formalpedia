-- Prove2me | solution 1 for PI.SqPairLocal.divAt_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:59:05.005409+00:00
-- url     : https://prove2.me/submissions/be72e327-7989-40e8-979e-d9941f160e77

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_DivAtOneOfInt
import Theorems.Thm_PI_SqPairLocal_divAt_mul_left

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
theorem _root_.solution {c : 𝓞 E} {a x : E} (hx : DivAt Q c x) (ha : IntAt Q a) : DivAt Q c (x * a) := by
  rw [mul_comm]
  exact divAt_mul_left ha hx
end PI.SqPairLocal
