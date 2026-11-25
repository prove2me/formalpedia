-- Prove2me | solution 1 for PI.SqPair.LCP.isUnit_ct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:21:38.552783+00:00
-- url     : https://prove2.me/submissions/ca06b1a4-6f67-4f7d-8452-7132d4ad0e01

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
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {u : Matrix ι ι R} (hu : IsUnit u.det) :
    IsUnit uᴴ := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [det_conjTranspose]; exact hu.star)
end PI.SqPair.LCP
