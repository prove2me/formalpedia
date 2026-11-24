-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Cusp.Fr.e33
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:41.681805+00:00
-- url     : https://prove2.me/submissions/09b8e0ca-93a8-4887-966d-8729c3f37d94

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_CuspidalAverages_FirstIdempotentAdjointThird
import Theorems.Thm_P2M_PositivityTheory_ThKEnd_Cusp_Fr_uv__9cf1dc9daa1c

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
theorem _root_.solution : e3 c J u u' * e3 c J u u' = e3 c J u u' := by
  simp [e3, Matrix.mul_assoc, ← Matrix.mul_assoc _ u', h.uv']
end PositivityTheory.ThKEnd.Cusp.Fr
