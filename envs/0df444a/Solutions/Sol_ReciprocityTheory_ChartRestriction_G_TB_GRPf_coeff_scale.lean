-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GRPf.coeff_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:50:13.229109+00:00
-- url     : https://prove2.me/submissions/ea9efbc8-b6a8-469f-bb73-f577e4518f21

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeRatio

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.GRPf
variable {O k T : Type} [CommRing O] [StarRing O] [CommRing k] [Algebra ℚ k] [Fintype T] {rk : T → ℕ}
  (χ : T → O →+* k)
namespace ReciprocityTheory.ChartRestriction.G.TB.GRPf
theorem _root_.solution (a : O) (f : MvPowerSeries (GLet T rk) k) (m : GLet T rk →₀ ℕ) :
    coeff m (scaleBy χ a f) = (m.prod fun l e => χ l.1 a ^ e) * coeff m f := by
  unfold scaleBy
  rw [MvPowerSeries.coeff_rescale]
end ReciprocityTheory.ChartRestriction.G.TB.GRPf
