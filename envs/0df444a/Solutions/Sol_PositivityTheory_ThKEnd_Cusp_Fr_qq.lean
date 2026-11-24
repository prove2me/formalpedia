-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Cusp.Fr.qq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:40.571639+00:00
-- url     : https://prove2.me/submissions/88f2ef14-ac47-41ca-9fdf-426707736908

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_CuspidalAverages_FirstIdempotentAdjointThird
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_e11
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_e13
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_e31
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_e33

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
theorem _root_.solution : (1 - e1 c J u u' - e3 c J u u') * (1 - e1 c J u u' - e3 c J u u') = 1 - e1 c J u u' - e3 c J u u' := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, h.e11, h.e13, h.e31, h.e33]
  abel
end PositivityTheory.ThKEnd.Cusp.Fr
