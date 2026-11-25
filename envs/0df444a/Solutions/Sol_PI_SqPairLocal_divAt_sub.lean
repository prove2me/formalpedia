-- Prove2me | solution 1 for PI.SqPairLocal.divAt_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:28:34.10534+00:00
-- url     : https://prove2.me/submissions/c1c037aa-9ea3-4148-9372-34541eea9f07

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_DivAtOneOfInt
import Theorems.Thm_PI_SqPairLocal_divAt_add
import Theorems.Thm_PI_SqPairLocal_divAt_neg

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
theorem _root_.solution {c : 𝓞 E} {x y : E} (hx : DivAt Q c x) (hy : DivAt Q c y) : DivAt Q c (x - y) := by
  rw [sub_eq_add_neg]
  exact divAt_add hx (divAt_neg hy)
end PI.SqPairLocal
