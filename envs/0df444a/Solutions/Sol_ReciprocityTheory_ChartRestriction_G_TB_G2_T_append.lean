-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.G2.T_append
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:31:33.287405+00:00
-- url     : https://prove2.me/submissions/2d4ba519-1ab5-4da1-a4af-2817ba147c8f

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
variable (F : Fin d → PS k 2 d) {ι : Type} (u : ι → Fin d → k)
namespace ReciprocityTheory.ChartRestriction.G.TB.G2
theorem _root_.solution (w w' : List ι) (A : PS k 1 d) : T F u (w ++ w') A = T F u w (T F u w' A) := by
  simp [T, List.foldr_append]
end ReciprocityTheory.ChartRestriction.G.TB.G2
