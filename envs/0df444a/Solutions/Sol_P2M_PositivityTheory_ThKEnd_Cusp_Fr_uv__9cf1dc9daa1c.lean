-- Prove2me | solution 1 for P2M_PositivityTheory_ThKEnd_Cusp_Fr_uv__9cf1dc9daa1c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:30.630001+00:00
-- url     : https://prove2.me/submissions/d3a0ca51-abd1-4a2d-975f-7a6d99695731

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
theorem _root_.solution : row c J u * u' = -1 := by
  rw [← map_map_c h.cc (row c J u * u'), Matrix.map_mul, h.row_c, Matrix.neg_mul, h.uv, Matrix.map_neg _ (map_neg c),
    Matrix.map_one _ (map_zero c) (map_one c)]
end PositivityTheory.ThKEnd.Cusp.Fr
