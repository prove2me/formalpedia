-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.mD_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:09:29.443563+00:00
-- url     : https://prove2.me/submissions/4b1f3fcd-adc9-43af-a0c1-e8bf01dae1cd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_lD_perm

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {φ : V → ℂ} {x : V} (hφ : ContDiffAt ℂ ω φ x) (l : List V) :
    mD φ x (l : Multiset V) = lD φ x l := lD_perm hφ (Multiset.coe_eq_coe.mp (Multiset.coe_toList _))
end ReciprocityTheory.ChartRestriction.G.PullbackSections
