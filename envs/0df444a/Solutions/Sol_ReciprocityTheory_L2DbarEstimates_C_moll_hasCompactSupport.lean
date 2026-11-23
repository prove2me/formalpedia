-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.moll_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:39.781915+00:00
-- url     : https://prove2.me/submissions/f15b01d6-5f76-4bd0-a5e1-c3f0911f12c9

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralBumpProfOnePos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_moll_tsupport

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
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution (n : ℕ) {t : ℝ} (ht : 0 < t) : HasCompactSupport (moll n t) := by
  exact (isCompact_closedBall (0 : V n) (t / 2)).of_isClosed_subset (isClosed_tsupport _)
    (moll_tsupport n ht)
end ReciprocityTheory.L2DbarEstimates.C
