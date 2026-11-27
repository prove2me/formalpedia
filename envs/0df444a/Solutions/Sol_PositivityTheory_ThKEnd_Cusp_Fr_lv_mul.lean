-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Cusp.Fr.lv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:27:33.554494+00:00
-- url     : https://prove2.me/submissions/2ebd4bdb-d0e3-41f4-8c38-69c3ff342c5c

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_CuspidalAverages_FirstIdempotentAdjointThird
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_v_lv
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_u_lv

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
theorem _root_.solution (g g' k k' : Matrix ι ι R) : lv c J u u' g g' * lv c J u u' k k' = lv c J u u' (g * k) (g' * k') := by
  conv_lhs => enter [1]; rw [lv]
  rw [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc _ (row c J u), h.v_lv, h.u_lv, Matrix.one_mul]
  simp only [lv, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one]
  abel
end PositivityTheory.ThKEnd.Cusp.Fr
