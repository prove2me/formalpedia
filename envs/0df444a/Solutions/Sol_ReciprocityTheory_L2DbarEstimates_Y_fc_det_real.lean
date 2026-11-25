-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fc_det_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:50:34.449378+00:00
-- url     : https://prove2.me/submissions/bdfcced6-c61c-42ec-b2e3-4ac59d955d54

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcC

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
open scoped ContDiff ENNReal
noncomputable section
universe u
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (n : ℕ) (J : V n →L[ℂ] V n) :
    |(J.restrictScalars ℝ).det| = ‖J.det‖ ^ 2 := by
  have h : (J.restrictScalars ℝ).det = Complex.normSq J.det := by
    show LinearMap.det ((J : V n →ₗ[ℂ] V n).restrictScalars ℝ) = _
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  rw [h, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
end ReciprocityTheory.L2DbarEstimates.Y
