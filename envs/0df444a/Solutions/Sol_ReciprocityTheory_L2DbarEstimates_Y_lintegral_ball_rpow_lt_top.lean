-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.lintegral_ball_rpow_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:39:32.781244+00:00
-- url     : https://prove2.me/submissions/5fcdac29-a179-447a-9c89-f39df2f5e4bc

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FamilyLeCoords
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_LintegralBallRpowLtTop

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
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} (hMVI : MVIntStatement n) (hn : 1 ≤ n) (vP : V n)
    {r : ℝ} (hr : r ≤ 1) {a : ℝ} (ha : a < n) :
    ∫⁻ v in Metric.ball vP r, ENNReal.ofReal ‖v - vP‖ ^ (-2 * a) < ⊤ := by
  have h0 := (hMVI hn a).2 ha
  have h1 : ∫⁻ v in Metric.ball vP r, ENNReal.ofReal ‖v - vP‖ ^ (-2 * a) ≤
      ∫⁻ v in Metric.ball vP 1, ENNReal.ofReal ‖v - vP‖ ^ (-2 * a) :=
    lintegral_mono_set (Metric.ball_subset_ball hr)
  have h2 : ∫⁻ v in Metric.ball vP 1, ENNReal.ofReal ‖v - vP‖ ^ (-2 * a) =
      ∫⁻ y in Metric.ball (0 : V n) 1, ENNReal.ofReal ‖y‖ ^ (-2 * a) := by
    rw [← lintegral_indicator Metric.isOpen_ball.measurableSet,
      ← lintegral_indicator Metric.isOpen_ball.measurableSet,
      ← lintegral_sub_right_eq_self ((Metric.ball (0 : V n) 1).indicator
        (fun y => ENNReal.ofReal ‖y‖ ^ (-2 * a))) vP]
    congr 1
    funext v
    by_cases hv : v ∈ Metric.ball vP 1
    · have hv' : v - vP ∈ Metric.ball (0 : V n) 1 := by
        rw [mem_ball_zero_iff]; rwa [Metric.mem_ball, dist_eq_norm] at hv
      rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv']
    · have hv' : v - vP ∉ Metric.ball (0 : V n) 1 := by
        rw [mem_ball_zero_iff]; rwa [Metric.mem_ball, dist_eq_norm] at hv
      rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv']
  exact lt_of_le_of_lt h1 (h2 ▸ h0)
end ReciprocityTheory.L2DbarEstimates.Y
