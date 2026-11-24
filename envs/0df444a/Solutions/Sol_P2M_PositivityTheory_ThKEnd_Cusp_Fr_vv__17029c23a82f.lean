-- Prove2me | solution 1 for P2M_PositivityTheory_ThKEnd_Cusp_Fr_vv__17029c23a82f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:07.336389+00:00
-- url     : https://prove2.me/submissions/662679bd-c50d-45b2-8f14-c7f5bc6bc2f7

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_CuspidalAverages_FirstIdempotentAdjointThird

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
theorem _root_.solution : row c J u' * u' = 0 := by
  rw [row]; nth_rw 2 [← transpose_transpose u']
  rw [← transpose_mul, ← Matrix.mul_assoc, h.vv, transpose_zero]
end PositivityTheory.ThKEnd.Cusp.Fr
