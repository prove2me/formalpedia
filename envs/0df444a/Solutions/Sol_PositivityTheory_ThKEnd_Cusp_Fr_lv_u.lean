-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Cusp.Fr.lv_u
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:50.884455+00:00
-- url     : https://prove2.me/submissions/a0075ba8-ffdb-4180-bf53-26fb20388c64

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_CuspidalAverages_FirstIdempotentAdjointThird
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_vu
import Theorems.Thm_P2M_PositivityTheory_ThKEnd_Cusp_Fr_uu__085486bb5a1a

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
theorem _root_.solution (g g' : Matrix ι ι R) : lv c J u u' g g' * u = u * g := by
  simp only [lv, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, h.vu, h.uu', Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero,
    Matrix.mul_sub]
  abel
end PositivityTheory.ThKEnd.Cusp.Fr
