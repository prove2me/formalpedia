-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.mollConst_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:28.893829+00:00
-- url     : https://prove2.me/submissions/ef0fe401-5dfe-4408-860f-48ef38b111f7

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralBumpProfOnePos

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
theorem _root_.solution (n : ℕ) : 0 ≤ mollConst n := by
  unfold mollConst
  exact inv_nonneg.mpr (integral_nonneg fun z => Real.smoothTransition.nonneg _)
end ReciprocityTheory.L2DbarEstimates.C
