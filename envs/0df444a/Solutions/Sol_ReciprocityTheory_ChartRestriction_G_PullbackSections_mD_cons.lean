-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.mD_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:34:30.948672+00:00
-- url     : https://prove2.me/submissions/b98d472a-9de4-48eb-b5c0-09d3e2d3dbd0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_lD_perm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_lD_cons

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
theorem _root_.solution {φ : V → ℂ} {x : V} (hφ : ContDiffAt ℂ ω φ x) (v : V) (s : Multiset V) :
    mD φ x (v ::ₘ s) =
      (iteratedFDeriv ℂ (s.toList.length + 1) φ x).curryLeft v (fun i => s.toList.get i) := by
  have hp : (v ::ₘ s).toList.Perm (v :: s.toList) := by
    rw [← Multiset.coe_eq_coe, Multiset.coe_toList, ← Multiset.cons_coe, Multiset.coe_toList]
  show lD φ x (v ::ₘ s).toList = _
  rw [lD_perm hφ hp, lD_cons]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
