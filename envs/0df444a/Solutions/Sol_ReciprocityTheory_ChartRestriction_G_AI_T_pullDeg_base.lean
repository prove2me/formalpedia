-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.T.pullDeg_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:25:30.883551+00:00
-- url     : https://prove2.me/submissions/5008ab77-e503-450d-bb84-edda8a94d459

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_DiagonalDivisors_ModelsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_DiagonalDivisors_InhabitBaseStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.T
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
universe u
namespace ReciprocityTheory.ChartRestriction.G.AI.T
theorem _root_.solution (c : YBlk → ℤ) (hc : c .line = 0) : pullDeg 0 c = pullDeg 1 c := by
  funext k
  cases k <;> simp [pullDeg, hc]
end ReciprocityTheory.ChartRestriction.G.AI.T
