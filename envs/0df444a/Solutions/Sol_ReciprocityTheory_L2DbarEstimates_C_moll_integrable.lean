-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.moll_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:24.970157+00:00
-- url     : https://prove2.me/submissions/ae6173ab-09e2-469a-8cd1-adf609174697

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MeasurableEmbeddingRotAbout
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegConv
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegIndep
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_moll_contDiff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_moll_hasCompactSupport


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
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution (n : ℕ) {t : ℝ} (ht : 0 < t) : Integrable (moll n t) := by
  exact (moll_contDiff n t).continuous.integrable_of_hasCompactSupport (moll_hasCompactSupport n ht)
end ReciprocityTheory.L2DbarEstimates.C
