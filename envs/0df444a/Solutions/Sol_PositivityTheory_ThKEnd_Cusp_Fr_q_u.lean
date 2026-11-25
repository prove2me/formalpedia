-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Cusp.Fr.q_u
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:00:36.178061+00:00
-- url     : https://prove2.me/submissions/cd9f88a8-8763-4694-9d4f-8fe015fcbded

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_CuspidalAverages_FirstIdempotentAdjointThird
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_first_idempotent_mul_vector
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_third_idempotent_mul_vector

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
theorem _root_.solution : (1 - e1 c J u u' - e3 c J u u') * u = 0 := by simp [Matrix.sub_mul, h.first_idempotent_mul_vector, h.third_idempotent_mul_vector]
end PositivityTheory.ThKEnd.Cusp.Fr
