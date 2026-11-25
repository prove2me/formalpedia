-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.fl3Test_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:14.927863+00:00
-- url     : https://prove2.me/submissions/360dc207-ed8f-424a-993c-e25df38bd721

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_ConstSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_IntegralMulLogZeroOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution : FlatnessTestCriterion := by
  intro c₁ c₂
  simp only
  constructor <;> ring
end ReciprocityTheory.ChartRestriction.G.AI
