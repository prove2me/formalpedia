-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.extCh_of_two_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:13.207143+00:00
-- url     : https://prove2.me/submissions/84ffde4f-b776-4e35-9327-2f93abb291b1

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
theorem _root_.solution {t : ℝ} (ht : 2 ≤ t) : extCh t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)
end ReciprocityTheory.L2DbarEstimates.C
