-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.dbv_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:25:57.913796+00:00
-- url     : https://prove2.me/submissions/5e03b986-b6ae-4ba8-b8da-f3a884386c48

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxD
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex Metric
open scoped ContDiff ENNReal ComplexConjugate
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} (c : ℂ) (D : V n →L[ℝ] ℂ) (ζ : V n) : dbv (c • D) ζ = c * dbv D ζ := by
  simp only [dbv, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring
end ReciprocityTheory.L2DbarEstimates.Y
