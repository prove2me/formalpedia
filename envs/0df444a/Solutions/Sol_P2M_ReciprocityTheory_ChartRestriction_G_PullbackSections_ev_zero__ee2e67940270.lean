-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_ev_zero__ee2e67940270
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:04.783802+00:00
-- url     : https://prove2.me/submissions/5ec6acf4-9b81-4728-a861-1c1e17ff2919

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped ContDiff
variable (R : Type) [CommRing R]
variable {R}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {m n d : ℕ} (a : Fin m → Pt R n d) : ev a (0 : PS R m d) = 0 := by
  first
  | exact map_zero _
  | (simp only [ev]; exact MvPowerSeries.subst_zero _)
  | simp [ev, MvPowerSeries.subst, MvPowerSeries.eval₂]
  | simp [ev, MvPowerSeries.subst]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
