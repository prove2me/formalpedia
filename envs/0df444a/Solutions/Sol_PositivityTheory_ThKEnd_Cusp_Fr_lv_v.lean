-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Cusp.Fr.lv_v
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:05.515804+00:00
-- url     : https://prove2.me/submissions/c3ad8574-c393-4dd6-b293-5702c194c8f3

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_CuspidalAverages_FirstIdempotentAdjointThird
import Theorems.Thm_P2M_PositivityTheory_ThKEnd_Cusp_Fr_vv__17029c23a82f
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
theorem _root_.solution (g g' : Matrix ι ι R) : lv c J u u' g g' * u' = u' * g' := by
  simp only [lv, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, h.vv', h.uv', Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero,
    Matrix.mul_sub, Matrix.mul_neg]
  abel
end PositivityTheory.ThKEnd.Cusp.Fr
