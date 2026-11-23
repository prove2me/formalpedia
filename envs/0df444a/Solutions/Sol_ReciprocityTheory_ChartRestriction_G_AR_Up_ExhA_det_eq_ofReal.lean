-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA.det_eq_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:15.119429+00:00
-- url     : https://prove2.me/submissions/3a4bb569-706a-43a1-90c6-e98a220fed38

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LiftFactorization
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetMonoDetOneAdd
import Definitions.Def_Lemmata_PosDefOfRealQuadratic_QuadFormRealSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhA_det_re_pos_im

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA
open Matrix
open scoped ComplexOrder Matrix
variable {p q : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA
theorem _root_.solution {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    A.det = ((A.det.re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simp [(det_re_pos_im hA).2])
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA
