-- Prove2me | solution 1 for PI.SqPairLocal.intAt_of_divAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:23:07.639136+00:00
-- url     : https://prove2.me/submissions/2bed7e00-8307-4ab0-bdbc-f0f4c8b7b503

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
namespace PI.SqPairLocal
theorem _root_.solution {Q : Ideal (𝓞 E)} (ϖ : 𝓞 E) {x : E} (h : DivAt Q (ϖ ^ 0) x) :
    IntAt Q x := by
  obtain ⟨s, hs, w, hw⟩ := h
  exact ⟨s, hs, w, by simpa using hw⟩
end PI.SqPairLocal
