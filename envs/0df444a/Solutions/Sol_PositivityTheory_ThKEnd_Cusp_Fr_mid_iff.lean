-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Cusp.Fr.mid_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:00:31.497926+00:00
-- url     : https://prove2.me/submissions/61940894-aa3f-4266-8938-abaa22e88697

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_CuspidalAverages_FirstIdempotentAdjointThird
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_qq

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
open PositivityTheory PositivityTheory.ThKEnd PositivityTheory.ThKEnd.Cusp
open Matrix
variable {R n ι : Type} [CommRing R] [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι] {c : R →+* R}
  {J x y x' y' : Matrix n n R} {u u' : Matrix n ι R}
open PositivityTheory.ThKEnd.Cusp.Fr
variable (h : Fr c J u u')
include h
namespace PositivityTheory.ThKEnd.Cusp.Fr
theorem _root_.solution (s : Matrix n n R) :
    mid c J u u' s = 1 ↔ (1 - e1 c J u u' - e3 c J u u') * (s - 1) * (1 - e1 c J u u' - e3 c J u u') = 0 := by
  rw [Matrix.mul_sub _ s, Matrix.sub_mul _ (_ * 1), Matrix.mul_one, h.qq, mid, sub_eq_zero]
  constructor <;> intro e
  · rw [← e]; nth_rw 1 [e]; nth_rw 1 [e]; abel
  · rw [e]; abel
end PositivityTheory.ThKEnd.Cusp.Fr
