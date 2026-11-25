-- Prove2me | solution 1 for PI.SqPair.LCP.cancel_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:26:36.400869+00:00
-- url     : https://prove2.me/submissions/e0ad5ae3-5f9b-4dd1-bb9d-54815d34d007

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_FiniteAdeleIdempotentOfFMulSelf
import Theorems.Thm_PI_SqPair_LCP_isUnit_ct

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
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {u X Y : Matrix ι ι R}
    (hu : IsUnit u.det) (h : uᴴ * X * u = uᴴ * Y * u) : X = Y := by
  have hU : IsUnit u := (Matrix.isUnit_iff_isUnit_det _).2 hu
  have h2 : uᴴ * X = uᴴ * Y := hU.mul_right_cancel h
  exact (isUnit_ct hu).mul_left_cancel h2
end PI.SqPair.LCP
