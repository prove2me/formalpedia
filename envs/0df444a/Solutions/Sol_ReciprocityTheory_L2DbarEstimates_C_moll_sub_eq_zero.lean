-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.moll_sub_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:08:41.750801+00:00
-- url     : https://prove2.me/submissions/dab9d1da-3002-42bc-b97e-05669e4cacad

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralBumpProfOnePos
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegConv
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
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {n : ℕ} {t : ℝ} (ht : 0 < t) {x y : V n}
    (hy : y ∉ closedBall x (t / 2)) : moll n t (x - y) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  apply hy
  have := moll_tsupport n ht h
  rw [mem_closedBall, dist_zero_right] at this
  rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
  exact this
end ReciprocityTheory.L2DbarEstimates.C
