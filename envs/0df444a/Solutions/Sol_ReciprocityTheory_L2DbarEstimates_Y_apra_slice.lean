-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.apra_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:34:28.421803+00:00
-- url     : https://prove2.me/submissions/e3b25803-23a7-4533-ac22-9bcb77f2e0fc

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_apraW_meas

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
theorem _root_.solution (d k : ℕ) (hMVd : MVStatement d) (ε τ : ℝ) (u : V d × V k → ℂ)
    (hu : DifferentiableOn ℂ u (ball (0 : V d) ε ×ˢ ball (0 : V k) ε)) (ζ : V k)
    (hζ : ζ ∈ ball (0 : V k) ε) :
    ENNReal.ofReal (‖u (0, ζ)‖ ^ 2) * ∫⁻ x : V d, apraW d ε τ ‖x‖ ≤
      ∫⁻ x in ball (0 : V d) ε,
        ENNReal.ofReal (‖u (x, ζ)‖ ^ 2 * (max (‖x‖ ^ 2) τ) ^ (-(d : ℝ))) := by
  have hdiff : DifferentiableOn ℂ (fun x : V d => u (x, ζ)) (ball 0 ε) :=
    hu.comp (differentiableOn_id.prodMk (differentiableOn_const ζ)) (fun x hx => ⟨hx, hζ⟩)
  have h := hMVd ε (fun x => u (x, ζ)) (apraW d ε τ) hdiff (apraW_meas d ε τ)
    (fun t ht => by simp [apraW, not_lt.mpr ht])
  refine h.trans (le_of_eq ?_)
  rw [← lintegral_indicator measurableSet_ball]
  refine lintegral_congr fun x => ?_
  by_cases hx : ‖x‖ < ε
  · have hx' : x ∈ ball (0 : V d) ε := mem_ball_zero_iff.mpr hx
    simp only [apraW, if_pos hx, Set.indicator_of_mem hx']
    rw [ENNReal.ofReal_mul (by positivity)]
  · have hx' : x ∉ ball (0 : V d) ε := fun h => hx (mem_ball_zero_iff.mp h)
    simp [apraW, hx]
end ReciprocityTheory.L2DbarEstimates.Y
