-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Cusp.Fr.mid_u
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:20:51.023527+00:00
-- url     : https://prove2.me/submissions/a6a42566-41d2-44fa-9aa5-135e9c463f47

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_CuspidalAverages_FirstIdempotentAdjointThird
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_first_idempotent_mul_vector
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_third_idempotent_mul_vector
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_q_u

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
theorem _root_.solution (s : Matrix n n R) : mid c J u u' s * u = u := by
  simp only [mid, Matrix.add_mul, Matrix.mul_assoc, h.q_u, h.first_idempotent_mul_vector, h.third_idempotent_mul_vector, Matrix.mul_zero, add_zero]
end PositivityTheory.ThKEnd.Cusp.Fr
