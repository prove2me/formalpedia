-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.apraW_anti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:35.173619+00:00
-- url     : https://prove2.me/submissions/dbc0228b-4c06-4c0a-b916-294f88dd4521

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Metric
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (d : ℕ) (ε : ℝ) {τ τ' : ℝ} (hτ : 0 < τ) (h : τ ≤ τ') (t : ℝ) :
    apraW d ε τ' t ≤ apraW d ε τ t := by
  unfold apraW
  split_ifs
  · exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (lt_max_of_lt_right hτ)
      (max_le_max le_rfl h) (neg_nonpos.mpr (Nat.cast_nonneg d)))
  · exact le_rfl
end ReciprocityTheory.L2DbarEstimates.Y
