-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.MV.ev_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:31:48.616934+00:00
-- url     : https://prove2.me/submissions/808ea31a-1d29-44c1-8c07-702ba2581602

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_MonoVal

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.MV
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k]
namespace ReciprocityTheory.ChartRestriction.G.TB.MV
theorem _root_.solution {d m n : ℕ} (a : Fin m → Pt k n d) : ev a (0 : PS k m d) = 0 := by
  have h := MvPowerSeries.subst_C (a := fun p : Fin m × Fin d => a p.1 p.2) (0 : k)
  rw [map_zero, map_zero] at h
  exact h
end ReciprocityTheory.ChartRestriction.G.TB.MV
