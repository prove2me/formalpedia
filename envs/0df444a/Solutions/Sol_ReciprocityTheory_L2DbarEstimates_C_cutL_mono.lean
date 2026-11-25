-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.cutL_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:02:44.471852+00:00
-- url     : https://prove2.me/submissions/78b44711-3043-49d5-94e2-4acd70df0756

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA

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
open scoped ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {ε s t : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) (hst : s ≤ t) : cutL ε s ≤ cutL ε t := by
  unfold cutL
  exact sub_le_sub_right (Real.log_le_log (by linarith) (by linarith)) _
end ReciprocityTheory.L2DbarEstimates.C
