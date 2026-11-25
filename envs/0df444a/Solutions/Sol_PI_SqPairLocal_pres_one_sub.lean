-- Prove2me | solution 1 for PI.SqPairLocal.pres_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:23:21.667214+00:00
-- url     : https://prove2.me/submissions/2f7be187-47a4-4086-8f3e-2f32112680d4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps

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
variable {N : ℕ}
namespace PI.SqPairLocal
theorem _root_.solution {L : Submodule (𝓞 E) (Fin N → E)} {e : Matrix (Fin N) (Fin N) E}
    (he : Pres L e) : Pres L (1 - e) := by
  intro y hy
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  exact L.sub_mem hy (he y hy)
end PI.SqPairLocal
