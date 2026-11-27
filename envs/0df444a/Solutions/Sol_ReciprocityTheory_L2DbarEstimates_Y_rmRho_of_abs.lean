-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.rmRho_of_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:30:59.283358+00:00
-- url     : https://prove2.me/submissions/ea0da396-6c07-4c06-adae-bbc8476784e8

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_RegMaxA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_rmRho_even
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_rmRho_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (t : ℝ) (h : 1 / 2 ≤ |t|) : rmRho t = |t| := by
  rcases le_or_gt 0 t with h0 | h0
  · rw [abs_of_nonneg h0] at h ⊢
    exact rmRho_of_le t h
  · rw [abs_of_neg h0] at h ⊢
    rw [← rmRho_even]
    exact rmRho_of_le (-t) h
end ReciprocityTheory.L2DbarEstimates.Y
