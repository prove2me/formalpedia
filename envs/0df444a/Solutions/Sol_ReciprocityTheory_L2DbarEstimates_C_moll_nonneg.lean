-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.moll_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:08:38.945914+00:00
-- url     : https://prove2.me/submissions/a530bda9-1492-4972-b79b-459b5c8f672a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralBumpProfOnePos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_mollConst_nonneg

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
theorem _root_.solution (n : ℕ) (t : ℝ) (z : V n) : 0 ≤ moll n t z := by
  have h : 0 ≤ t ^ (2 * n) := by rw [pow_mul]; positivity
  exact mul_nonneg (mul_nonneg (mollConst_nonneg n) (inv_nonneg.mpr h)) (Real.smoothTransition.nonneg _)
end ReciprocityTheory.L2DbarEstimates.C
