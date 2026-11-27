-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Cusp.Fr.mid_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:22:35.572236+00:00
-- url     : https://prove2.me/submissions/f895bfdb-dd88-4ed7-8c38-f85073bf97ed

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_CuspidalAverages_FirstIdempotentAdjointThird
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_e11
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_e13
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_e31
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_e33
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
theorem _root_.solution (s : Matrix n n R) : mid c J u u' (mid c J u u' s) = mid c J u u' s := by
  have q1 : (1 - e1 c J u u' - e3 c J u u') * e1 c J u u' = 0 := by simp [Matrix.sub_mul, h.e11, h.e31]
  have q2 : (1 - e1 c J u u' - e3 c J u u') * e3 c J u u' = 0 := by simp [Matrix.sub_mul, h.e13, h.e33]
  conv_lhs => rw [mid, mid, Matrix.mul_add, Matrix.mul_add, q1, q2, zero_add, add_zero, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h.qq,
    Matrix.mul_assoc _ _ (1 - _ - _), h.qq]
  rfl
end PositivityTheory.ThKEnd.Cusp.Fr
