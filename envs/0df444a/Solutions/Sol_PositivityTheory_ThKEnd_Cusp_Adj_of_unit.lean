-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Cusp.Adj.of_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:23:55.892202+00:00
-- url     : https://prove2.me/submissions/3794c568-4024-4d39-97e2-9703e3c749ee

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
theorem _root_.solution (h : xᵀ * J * x.map c = J) (e : x * y = 1) : Adj c J x y := by
  unfold Adj
  conv_rhs => rw [← h]
  rw [Matrix.mul_assoc, ← Matrix.map_mul, e, Matrix.map_one _ (map_zero c) (map_one c), Matrix.mul_one]
end Adj
end PositivityTheory.ThKEnd.Cusp
