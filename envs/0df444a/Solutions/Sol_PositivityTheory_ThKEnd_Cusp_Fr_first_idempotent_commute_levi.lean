-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Cusp.Fr.first_idempotent_commute_levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:00:25.859752+00:00
-- url     : https://prove2.me/submissions/5206f056-6676-4276-8e7e-da60ceb71ec5

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_CuspidalAverages_FirstIdempotentAdjointThird
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_lv_u
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_v_lv

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
theorem _root_.solution (g g' : Matrix ι ι R) : e1 c J u u' * lv c J u u' g g' = lv c J u u' g g' * e1 c J u u' := by
  rw [e1, Matrix.mul_assoc, h.v_lv, ← Matrix.mul_assoc (lv c J u u' g g'), h.lv_u, Matrix.mul_assoc]
end PositivityTheory.ThKEnd.Cusp.Fr
