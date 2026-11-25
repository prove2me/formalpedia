-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.unwBack_exp_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:15:59.993401+00:00
-- url     : https://prove2.me/submissions/b5fa987f-f02b-4c11-b374-83993209b119

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (a : ℝ) : Real.exp a ^ 2 * Real.exp (-a) = Real.exp a := by
  rw [sq, mul_assoc, ← Real.exp_add]
  simp
end ReciprocityTheory.L2DbarEstimates.F
