-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.ptx_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:01.346004+00:00
-- url     : https://prove2.me/submissions/f32001d9-8105-4b85-bc80-4a72e96a5be0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CardToMultisetEqDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_EqZeroOfVecMulTmat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_LgCurvePcurve

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
theorem _root_.solution (G : LogFGL v d) (p : ℕ) (γ : Fin d → Fin d → PowerSeries C)
    (ga : Fin d → PowerSeries C) (n : ℕ) :
    ptx G p γ ga n = Matrix.vecMul (ptw G p γ ga n) (tmat γ)⁻¹ := by
  rw [ptx, ptw, Finset.sum_range]
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
