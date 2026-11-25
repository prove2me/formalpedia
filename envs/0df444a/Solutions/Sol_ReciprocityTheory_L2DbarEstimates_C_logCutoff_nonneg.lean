-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.logCutoff_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:14:22.034676+00:00
-- url     : https://prove2.me/submissions/cd5d2b0b-a554-45c7-b7bb-4c570193dbf6

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeakA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_extCh_nonneg

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
theorem _root_.solution (F : V n → ℂ) (k : ℝ) (z : V n) : 0 ≤ extCut F k z := by
  unfold extCut
  split_ifs
  · exact le_rfl
  · exact extCh_nonneg _
end ReciprocityTheory.L2DbarEstimates.C
