-- Prove2me | solution 1 for PI.SqPairLocal.divAt_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:47:22.720395+00:00
-- url     : https://prove2.me/submissions/a664a1b2-6693-48dc-8a34-322a30593374

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_DivAtOneOfInt
import Theorems.Thm_PI_SqPairLocal_mul_nmem

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
theorem _root_.solution {c : 𝓞 E} {a x : E} (ha : IntAt Q a) (hx : DivAt Q c x) : DivAt Q c (a * x) := by
  unfold IntAt at ha
  unfold DivAt at *
  obtain ⟨s, hs, w, hw⟩ := ha
  obtain ⟨t, ht, v, hv⟩ := hx
  refine ⟨s * t, mul_nmem hs ht, w * v, ?_⟩
  push_cast
  linear_combination ((t : E) * x) * hw + (w : E) * hv
end PI.SqPairLocal
