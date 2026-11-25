-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA.det_re_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:31:37.626549+00:00
-- url     : https://prove2.me/submissions/b4507941-f808-4acd-af83-c7ec4be5c013

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LiftFactorization
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetMonoDetOneAdd
import Definitions.Def_Lemmata_PosDefOfRealQuadratic_QuadFormRealSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_maDet


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
theorem _root_.solution {Z : Matrix (Fin p) (Fin q) ℂ} (hZ : (1 - Z * Zᴴ).PosDef) :
    (1 - Z * Zᴴ).det.re ≤ 1 := by
  have hm := ReciprocityTheory.L2DbarEstimates.I.maDet p 1 (1 - Z * Zᴴ) hZ.posSemidef
    (by rw [sub_sub_cancel]; exact posSemidef_self_mul_conjTranspose Z)
  simpa using hm
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA
