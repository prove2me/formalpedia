-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Cusp.Fr.lv_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:00:29.430671+00:00
-- url     : https://prove2.me/submissions/264d43eb-90a8-4fac-8118-2df1555eca86

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_CuspidalAverages_FirstIdempotentAdjointThird
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_lv_u
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_lv_v

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
theorem _root_.solution (g g' : Matrix ι ι R) :
    lv c J u u' g g' * (1 - e1 c J u u' - e3 c J u u') = 1 - e1 c J u u' - e3 c J u u' := by
  rw [e1, e3, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h.lv_u, h.lv_v]
  simp only [lv, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  abel
end PositivityTheory.ThKEnd.Cusp.Fr
