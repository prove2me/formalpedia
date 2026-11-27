-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.T.pullDeg_twoXiDegY
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:25:36.190792+00:00
-- url     : https://prove2.me/submissions/000c75d7-97a2-4164-81bb-7287f1361978

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
theorem _root_.solution (j : Fin 2) : pullDeg j twoXiDegY = twoXiDeg j := by
  funext k
  fin_cases j <;> cases k <;> simp [pullDeg, twoXiDegY, twoXiDeg, unitDeg]
end ReciprocityTheory.ChartRestriction.G.AI.T
