-- Prove2me | solution 1 for PI.SqPairLocal.divAt_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:47:21.6307+00:00
-- url     : https://prove2.me/submissions/262deb45-9b7a-4581-b4b1-1cef9ecf02ca

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
theorem _root_.solution {c : 𝓞 E} {x y : E} (hx : DivAt Q c x) (hy : DivAt Q c y) : DivAt Q c (x + y) := by
  unfold DivAt at *
  obtain ⟨s, hs, w, hw⟩ := hx
  obtain ⟨t, ht, v, hv⟩ := hy
  refine ⟨s * t, mul_nmem hs ht, t * w + s * v, ?_⟩
  push_cast
  linear_combination (t : E) * hw + (s : E) * hv
end PI.SqPairLocal
