-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.TM.mD_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:26.462729+00:00
-- url     : https://prove2.me/submissions/909127aa-d285-4591-8d92-7f5b754bf09c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorMul

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.TM
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped ContDiff Topology
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.TM
theorem _root_.solution (θ : (Fin g → ℂ) → ℂ) : mD θ 0 0 = θ 0 := by
  have key : ∀ l : List (Fin g → ℂ), l = [] →
      iteratedFDeriv ℂ l.length θ 0 (fun i => l.get i) = θ 0 := by
    rintro l rfl
    simp
  exact key _ (Multiset.toList_eq_nil.2 rfl)
end ReciprocityTheory.ChartRestriction.G.PullbackSections.TM
