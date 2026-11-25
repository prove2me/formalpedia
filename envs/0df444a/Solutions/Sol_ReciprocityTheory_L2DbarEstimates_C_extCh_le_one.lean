-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.extCh_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:14:22.014121+00:00
-- url     : https://prove2.me/submissions/9a351cb4-409e-4839-b3a1-9dfe8dfc3739

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeakA

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
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution (t : ℝ) : extCh t ≤ 1 := Real.smoothTransition.le_one _
end ReciprocityTheory.L2DbarEstimates.C
