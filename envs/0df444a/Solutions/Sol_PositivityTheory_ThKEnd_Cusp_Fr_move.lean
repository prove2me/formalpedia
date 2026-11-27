-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Cusp.Fr.move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:20:55.847506+00:00
-- url     : https://prove2.me/submissions/04266326-d989-4c76-9201-a81fc00efc8a

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_CuspidalAverages_FirstIdempotentAdjointThird
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_vu
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_row_mul
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_mid_iff

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
theorem _root_.solution {s s' : Matrix n n R} (hs : Adj c J s s') (a : s * u = u) (a' : s' * u = u) (b : mid c J u u' s = 1) :
    (s - 1) * (1 - e3 c J u u') = u * (row c J u' * (s - 1) * (1 - e3 c J u u')) := by
  have h1 : (s - 1) * e1 c J u u' = 0 := by rw [e1, ← Matrix.mul_assoc, Matrix.sub_mul, a, Matrix.one_mul, sub_self, Matrix.zero_mul]
  have h2 : e3 c J u u' * (s - 1) = 0 := by
    have := h.row_mul hs (g := 1) (by rw [a', Matrix.mul_one])
    rw [Matrix.map_one _ (map_zero c) (map_one c), transpose_one, Matrix.one_mul] at this
    rw [e3, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_sub, this, Matrix.mul_one, sub_self, Matrix.mul_zero, neg_zero]
  have h3 := (h.mid_iff s).1 b
  rw [sub_right_comm 1 (e1 c J u u'), Matrix.mul_sub _ (1 - _), Matrix.mul_assoc _ _ (e1 c J u u'), h1, Matrix.mul_zero, sub_zero,
    Matrix.sub_mul, Matrix.sub_mul 1, h2, Matrix.one_mul, sub_zero, Matrix.sub_mul, sub_eq_zero] at h3
  rw [h3, e1]
  conv_rhs => rw [Matrix.mul_assoc, h3, e1]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc u _ u, h.vu, Matrix.mul_one]
end PositivityTheory.ThKEnd.Cusp.Fr
