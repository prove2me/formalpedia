-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.ordGE_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:59.041828+00:00
-- url     : https://prove2.me/submissions/2a8e28c5-2672-49e4-86c4-d41e90a9616e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChgPfTP

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
open ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
variable {k : Type} [CommRing k]
namespace ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
theorem _root_.solution {σ : Type} (g : MvPowerSeries σ k) : OrdGE 0 g := fun e he => absurd he (Nat.not_lt_zero _)
end ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
