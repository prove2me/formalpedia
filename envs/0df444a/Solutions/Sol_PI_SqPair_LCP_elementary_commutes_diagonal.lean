-- Prove2me | solution 1 for PI.SqPair.LCP.elementary_commutes_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:22:30.475196+00:00
-- url     : https://prove2.me/submissions/749e0d41-449f-49d7-8e0b-4befa9bb7980

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
theorem _root_.solution (d : Fin 2 → R) :
    (e0 : Matrix (Fin 2) (Fin 2) R) * diagonal d = diagonal d * e0 := by
  rw [e0, diagonal_mul_diagonal, diagonal_mul_diagonal]; congr 1; ext i; ring
end PI.SqPair.LCP
