-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.T.two_llDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:29:02.361143+00:00
-- url     : https://prove2.me/submissions/cdf76400-70f6-46c4-ad95-e429e30b438e

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
theorem _root_.solution : 2 • llDeg = -(twoXiDeg 0 + twoXiDeg 1) := by
  funext k
  cases k <;> simp [llDeg, twoXiDeg, unitDeg]
end ReciprocityTheory.ChartRestriction.G.AI.T
