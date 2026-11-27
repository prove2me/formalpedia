-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Two.Dual.embY
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:21:28.190534+00:00
-- url     : https://prove2.me/submissions/3547c481-21a3-4fa5-8f5b-5be38d06374d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_EmbMMul
import Theorems.Thm_PositivityTheory_ThKEnd_Two_embM_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKEnd PositivityTheory.ThKEnd.Two
open Matrix GlobalTheory.WeilM
variable {S R d k : Type} [CommRing S] [CommRing R] [Algebra S R] [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
variable {c : R →ₐ[S] R} {J : Matrix d d R} {X Y : Matrix d k R}
namespace PositivityTheory.ThKEnd.Two
namespace Dual
theorem _root_.solution (h : Dual c J X Y) (g g' : Matrix k k R) : embM c J X Y g g' * Y = Y * g' := by
  rw [embM_mul, h.yy, h.yx]
  simp only [transpose_zero, transpose_neg, transpose_one, Matrix.mul_zero, Matrix.mul_neg, Matrix.mul_one, add_zero,
    sub_neg_eq_add, Matrix.mul_sub]
  abel
end Dual
end PositivityTheory.ThKEnd.Two
