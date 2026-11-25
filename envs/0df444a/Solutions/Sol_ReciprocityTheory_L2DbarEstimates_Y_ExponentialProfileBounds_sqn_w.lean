-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds.sqn_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:26:40.601062+00:00
-- url     : https://prove2.me/submissions/c268b8e3-c452-435a-8117-1828aa79473e

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_EuclideanAtlasPointwiseNormSqUnitSection
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ExponentialProfileBounds_nsq_eq
import Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_Y_ExponentialProfileBounds_norm_sq_eq__466fb63a3492

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Matrix
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds
theorem _root_.solution (y : V n) : (atlas n).sqn 1 (wI n) y = 1 := by
  simp only [WeightedAtlas.sqn, nsq_eq, wI, ← Finset.sum_mul, Fin.sum_univ_succ, wv, Fin.cons_zero,
    Fin.cons_succ, norm_one, one_pow]
  rw [← norm_sq_eq', mul_inv_cancel₀ (pos_one_add y).ne']
end ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds
