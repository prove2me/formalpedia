-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Cusp.Adj.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:00:20.727262+00:00
-- url     : https://prove2.me/submissions/ce3e0e5c-eb1b-4905-8149-b42d7e7901f8

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
namespace PositivityTheory.ThKEnd.Cusp
namespace Adj
theorem _root_.solution (h : Adj c J x y) (h' : Adj c J x' y') : Adj c J (x * x') (y' * y) := by
  rw [Adj, transpose_mul, Matrix.mul_assoc, h, ← Matrix.mul_assoc, h', Matrix.map_mul, Matrix.mul_assoc]
end Adj
end PositivityTheory.ThKEnd.Cusp
