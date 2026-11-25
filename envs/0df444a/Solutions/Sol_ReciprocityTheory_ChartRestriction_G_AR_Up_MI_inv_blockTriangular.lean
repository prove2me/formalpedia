-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.inv_blockTriangular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:33:01.95893+00:00
-- url     : https://prove2.me/submissions/c38e35f3-337d-4253-8dce-7a7fbde14416

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
import Definitions.Def_Lemmata_GeneralBFactForm_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution {α : Type*} [LinearOrder α] {b : Fin n → α} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.BlockTriangular b) (hd : M.det ≠ 0) : (M⁻¹).BlockTriangular b := by
  haveI : Invertible M := M.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hd)
  exact Matrix.blockTriangular_inv_of_blockTriangular hM
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
