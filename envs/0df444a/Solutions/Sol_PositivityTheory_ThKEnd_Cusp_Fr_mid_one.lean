-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Cusp.Fr.mid_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:20:46.101807+00:00
-- url     : https://prove2.me/submissions/a9413858-5529-44bc-bbe5-8667a1633f3a

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_CuspidalAverages_FirstIdempotentAdjointThird
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_e11
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_e13
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_e31
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_e33

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
theorem _root_.solution : mid c J u u' 1 = 1 := by
  have h11 := h.e11
  have h13 := h.e13
  have h31 := h.e31
  have h33 := h.e33
  simp only [mid, Matrix.mul_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, h11, h13, h31, h33]
  abel
end PositivityTheory.ThKEnd.Cusp.Fr
