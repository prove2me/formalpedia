-- Prove2me | solution 1 for PI.SqPair.LCP.finiteAdeleIdempotentOfF_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:22:40.637876+00:00
-- url     : https://prove2.me/submissions/96cf8e52-cabb-4d71-839f-1eb460db7307

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
theorem _root_.solution : (e0 : Matrix (Fin 2) (Fin 2) R) * e0 = e0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e0]
end PI.SqPair.LCP
