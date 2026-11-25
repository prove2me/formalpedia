-- Prove2me | solution 1 for PI.SqPair.LCP.elementary_hyperbolic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:22:35.269433+00:00
-- url     : https://prove2.me/submissions/79ebd324-ff32-4e21-83a0-e1556acc12dc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_FiniteAdeleIdempotentOfFMulSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LCP
variable {R : Type} [CommRing R] [StarRing R]
namespace PI.SqPair.LCP
theorem _root_.solution : (e0 : Matrix (Fin 2) (Fin 2) R)ᴴ * hyp = hyp - hyp * e0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [e0, hyp, Matrix.mul_apply, Fin.sum_univ_two, vecMul, dotProduct, diagonal_apply]
end PI.SqPair.LCP
