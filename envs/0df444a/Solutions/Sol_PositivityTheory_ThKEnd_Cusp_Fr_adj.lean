-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Cusp.Fr.adj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:33.433311+00:00
-- url     : https://prove2.me/submissions/559138cf-1fbc-481b-89c8-b588ef45e70a

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_CuspidalAverages_FirstIdempotentAdjointThird
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_map_map_c
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_row_c

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
theorem _root_.solution (w w' : Matrix n ι R) (g : Matrix ι ι R) : Adj c J (w * g * row c J w') (-(w' * (g.map c)ᵀ * row c J w)) := by
  rw [Adj, Matrix.map_neg _ (map_neg c), Matrix.map_mul, Matrix.map_mul, h.row_c, transpose_map, map_map_c h.cc, row]
  simp only [transpose_mul, transpose_transpose, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
end PositivityTheory.ThKEnd.Cusp.Fr
