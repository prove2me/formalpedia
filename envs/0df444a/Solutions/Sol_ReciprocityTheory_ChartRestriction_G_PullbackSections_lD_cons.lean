-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.lD_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:27:15.847091+00:00
-- url     : https://prove2.me/submissions/7bea67c3-f7d7-4671-84f7-0d200ae6671f

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (φ : V → ℂ) (x v : V) (l : List V) :
    lD φ x (v :: l) = (iteratedFDeriv ℂ (l.length + 1) φ x).curryLeft v (fun i => l.get i) := by
  show iteratedFDeriv ℂ (l.length + 1) φ x (fun i => (v :: l).get i) = _
  rw [ContinuousMultilinearMap.curryLeft_apply]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · first | rfl | simp
  · first | rfl | simp
end ReciprocityTheory.ChartRestriction.G.PullbackSections
