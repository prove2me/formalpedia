-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Cusp.Fr.third_idempotent_adjoint_first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:00:06.219942+00:00
-- url     : https://prove2.me/submissions/c8f4492b-a233-4b35-948a-f8a8076e5f17

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_CuspidalAverages_FirstIdempotentAdjointThird
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Adj_one
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Adj_sub
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_adj

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
theorem _root_.solution : Adj c J (e3 c J u u') (e1 c J u u') := by
  have := (Adj.one.sub Adj.one).sub (h.adj u' u 1)
  simpa [e1, e3, Matrix.map_one _ (map_zero c) (map_one c)] using this
end PositivityTheory.ThKEnd.Cusp.Fr
