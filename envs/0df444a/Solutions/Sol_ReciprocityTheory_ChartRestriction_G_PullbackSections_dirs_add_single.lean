-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.dirs_add_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:27:59.662883+00:00
-- url     : https://prove2.me/submissions/9494b0f6-e731-443a-81c6-b0f9e923bc6c

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
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (n : Fin 1 × Fin g →₀ ℕ) (p : Fin 1 × Fin g) :
    dirs (n + Finsupp.single p 1) = Pi.single p.2 1 ::ₘ dirs n := by
  first
  | (simp only [dirs, map_add, Finsupp.toMultiset_single, one_nsmul, Multiset.map_add, Multiset.map_singleton]
     rw [add_comm, Multiset.singleton_add])
  | simp [dirs, Finsupp.toMultiset_add, add_comm]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
