-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Cusp.Fr.mid_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:20:41.931847+00:00
-- url     : https://prove2.me/submissions/ac668400-f740-41d1-ace8-07793560a56d

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
theorem _root_.solution {s s' : Matrix n n R} (a : s * e1 c J u u' = e1 c J u u') (b : e3 c J u u' * s' = e3 c J u u') :
    mid c J u u' (s * s') = mid c J u u' s * mid c J u u' s' := by
  have h11 := h.e11
  have h13 := h.e13
  have h31 := h.e31
  have h33 := h.e33
  rw [mid, mid, mid]
  generalize e1 c J u u' = p at *
  generalize e3 c J u u' = r at *
  have q1 : (1 - p - r) * p = 0 := by simp [Matrix.sub_mul, h11, h31]
  have q2 : (1 - p - r) * r = 0 := by simp [Matrix.sub_mul, h13, h33]
  have q3 : p * (1 - p - r) = 0 := by simp [Matrix.mul_sub, h11, h13]
  have q4 : r * (1 - p - r) = 0 := by simp [Matrix.mul_sub, h31, h33]
  have q5 : (1 - p - r) * (1 - p - r) = 1 - p - r := by
    nth_rw 1 [Matrix.sub_mul, Matrix.sub_mul, q3, q4]; simp
  have q6 : (1 - p - r) * s * (1 - p - r) * s' * (1 - p - r) = (1 - p - r) * (s * s') * (1 - p - r) := by
    nth_rw 2 [Matrix.mul_sub]
    rw [Matrix.mul_sub _ 1, Matrix.mul_assoc _ s p, a, q1, Matrix.sub_mul, Matrix.sub_mul _ _ s', Matrix.sub_mul,
      Matrix.mul_assoc _ r s', b, Matrix.mul_assoc _ r, q4]
    simp [Matrix.mul_assoc]
  generalize 1 - p - r = q at *
  have a1 : q * s * q * p = 0 := by rw [Matrix.mul_assoc, q1, Matrix.mul_zero]
  have a2 : q * s * q * r = 0 := by rw [Matrix.mul_assoc, q2, Matrix.mul_zero]
  simp only [Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_assoc, h11, h13, h31, h33, q3, q4, a1, a2, Matrix.zero_mul, add_zero, zero_add]
  rw [Matrix.mul_assoc (q * s) q q, q5, q6, Matrix.mul_assoc q s s']
end PositivityTheory.ThKEnd.Cusp.Fr
