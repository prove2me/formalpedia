-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_single_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:18.471784+00:00
-- url     : https://prove2.me/submissions/4317547a-e8d8-4e62-9890-e6824d6696e2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable (A : Type) [CommRing A] [Algebra ℚ A]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution (e : Fin 2 →₀ ℕ) : e = single 0 (e 0) + single 1 (e 1) := by
  ext j
  fin_cases j <;> simp [Finsupp.single_apply]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
