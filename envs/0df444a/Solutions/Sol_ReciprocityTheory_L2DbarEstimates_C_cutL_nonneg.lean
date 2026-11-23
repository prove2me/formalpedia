-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.cutL_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:40.11411+00:00
-- url     : https://prove2.me/submissions/dfea083b-9e57-470c-a2f5-a04ae84f3bef

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
theorem _root_.solution {ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) : 0 ≤ cutL ε s := by
  unfold cutL
  exact sub_nonneg.2 (Real.log_le_log hε (by linarith))
end ReciprocityTheory.L2DbarEstimates.C
