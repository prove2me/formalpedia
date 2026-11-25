-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.dAdd_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:33:22.87152+00:00
-- url     : https://prove2.me/submissions/629418a0-6c77-4daa-9981-bb9e7af4b4e8

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
theorem _root_.solution (u : Fin d → k) (b : Fin n) (a : k) : dAdd u b (C a : PS k n d) = 0 := by
  unfold dAdd
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [show (C a : PS k n d) = algebraMap k (PS k n d) a from rfl, Derivation.map_algebraMap, mul_zero]
end ReciprocityTheory.ChartRestriction.G.TB
