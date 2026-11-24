-- Prove2me | solution 1 for P2M_PI_SqPairLocal_StModel___ne_57ec0e9aa56c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:35:04.304594+00:00
-- url     : https://prove2.me/submissions/b163d747-b2ff-4188-b6ee-99238361083f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IntAtOfDivAtZero

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
open PI.SqPair
attribute [local instance] StModel.cr StModel.dom StModel.dvr StModel.hens StModel.fin
variable {E : Type} [Field E] [NumberField E] [StarRing E]
open PI.SqPairLocal.StModel
variable {Q : Ideal (𝓞 E)} (M : StModel E Q)
namespace PI.SqPairLocal.StModel
theorem _root_.solution : M.ϖ ≠ 0 := by
  intro h
  apply M.ϖ_irr.ne_zero
  apply Subtype.ext
  simp [h]
end PI.SqPairLocal.StModel
