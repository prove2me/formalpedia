-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.G2.dof_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:30:24.898381+00:00
-- url     : https://prove2.me/submissions/78e293ee-796f-426d-80c6-63d66c4a7a7a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofListSum

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.G2
variable {k : Type} [CommRing k] {d : ℕ}
variable (F : Fin d → PS k 2 d) (v : Fin d → k)
namespace ReciprocityTheory.ChartRestriction.G.TB.G2
theorem _root_.solution : Dof F v (0 : PS k 1 d) = 0 := by
  simp [Dof]
end ReciprocityTheory.ChartRestriction.G.TB.G2
