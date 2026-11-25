-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.dAdd_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:33:28.276007+00:00
-- url     : https://prove2.me/submissions/6ad45f4f-1a67-4c10-ba57-6af82148ab27

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_KillAddQ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FoldrIterateEqTG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_KillAdd

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.G2
variable {k : Type} [CommRing k] {d n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB
theorem _root_.solution (u : Fin d → k) (b : Fin n) (f g : PS k n d) : dAdd u b (f + g) = dAdd u b f + dAdd u b g := by
  simp only [dAdd, map_add, mul_add, Finset.sum_add_distrib]
end ReciprocityTheory.ChartRestriction.G.TB
