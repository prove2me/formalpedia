-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.tmat_isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:06:53.8048+00:00
-- url     : https://prove2.me/submissions/b2d0bd3d-ce15-47b8-bcd9-38bdbec651f1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_EqZeroOfVecMulTmat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_tmat_det_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
theorem _root_.solution {γ : Fin d → Fin d → PowerSeries C} (hdet : v (tmat γ).det = 0) :
    IsUnit (tmat γ).det := isUnit_iff_ne_zero.mpr (tmat_det_ne_zero hdet)
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
