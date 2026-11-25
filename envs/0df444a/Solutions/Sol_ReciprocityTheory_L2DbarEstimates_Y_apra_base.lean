-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.apra_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:35:06.936391+00:00
-- url     : https://prove2.me/submissions/15df87ff-3d06-49c4-b264-f1630d30723a

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
theorem _root_.solution (k : ℕ) (hMVk : MVStatement k) (ε : ℝ) (g : V k → ℂ)
    (hg : DifferentiableOn ℂ g (ball 0 ε)) :
    ENNReal.ofReal (‖g 0‖ ^ 2) * volume (ball (0 : V k) ε) ≤
      ∫⁻ ζ in ball (0 : V k) ε, ENNReal.ofReal (‖g ζ‖ ^ 2) := by
  have h := hMVk ε g (fun t => if t < ε then 1 else 0) hg
    (Measurable.ite measurableSet_Iio measurable_const measurable_const)
    (fun t ht => by simp [not_lt.mpr ht])
  have e1 : ∫⁻ y : V k, (fun t : ℝ => if t < ε then (1 : ℝ≥0∞) else 0) ‖y‖ =
      volume (ball (0 : V k) ε) := by
    rw [← lintegral_indicator_one measurableSet_ball]
    refine lintegral_congr fun y => ?_
    by_cases hy : ‖y‖ < ε <;> simp [hy, Set.indicator]
  have e2 : ∫⁻ y : V k, ENNReal.ofReal (‖g y‖ ^ 2) *
      (fun t : ℝ => if t < ε then (1 : ℝ≥0∞) else 0) ‖y‖ =
      ∫⁻ ζ in ball (0 : V k) ε, ENNReal.ofReal (‖g ζ‖ ^ 2) := by
    rw [← lintegral_indicator measurableSet_ball]
    refine lintegral_congr fun y => ?_
    by_cases hy : ‖y‖ < ε <;> simp [hy, Set.indicator]
  rw [e1, e2] at h
  exact h
end ReciprocityTheory.L2DbarEstimates.Y
