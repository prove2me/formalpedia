-- Prove2me | solution 1 for PI.SqPairLocal.divAt_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:23:12.547629+00:00
-- url     : https://prove2.me/submissions/3521fba1-4c5e-42d9-b0a6-aab4f64eae80

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
theorem _root_.solution {c : 𝓞 E} {x : E} (hx : DivAt Q c x) : DivAt Q c (-x) := by
  unfold DivAt at *
  obtain ⟨s, hs, w, hw⟩ := hx
  refine ⟨s, hs, -w, ?_⟩
  push_cast
  linear_combination -hw
end PI.SqPairLocal
