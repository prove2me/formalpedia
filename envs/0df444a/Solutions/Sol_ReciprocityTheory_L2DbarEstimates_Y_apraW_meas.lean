-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.apraW_meas
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:35.386211+00:00
-- url     : https://prove2.me/submissions/b23f1bc9-5c31-4c16-b128-93e8168c8049

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
theorem _root_.solution (d : ℕ) (ε τ : ℝ) : Measurable (apraW d ε τ) := by
  unfold apraW
  refine Measurable.ite measurableSet_Iio ?_ measurable_const
  exact ENNReal.measurable_ofReal.comp
    (((measurable_id.pow_const 2).max measurable_const).pow_const _)
end ReciprocityTheory.L2DbarEstimates.Y
