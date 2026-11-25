-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.logCutoff_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:43:24.058922+00:00
-- url     : https://prove2.me/submissions/0a626928-b2cc-42db-a7d6-2dec8282ad7b

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeakA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_extCh_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal ContDiff
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution (F : V n → ℂ) (k : ℝ) (z : V n) : extCut F k z ≤ 1 := by
  unfold extCut
  split_ifs
  · exact zero_le_one
  · exact extCh_le_one _
end ReciprocityTheory.L2DbarEstimates.C
