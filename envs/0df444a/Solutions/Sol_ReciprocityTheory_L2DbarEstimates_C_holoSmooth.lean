-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.holoSmooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:08:28.516686+00:00
-- url     : https://prove2.me/submissions/23b9b5fd-f907-4fca-a9d3-3bd834c78eef

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloContDiffStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralMollProfBall
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MollifyEqConvolution
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_mollify_eq_convolution
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_holo_eq_mollify
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_moll_contDiff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_moll_eq_zero_of_lt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_moll_hasCompactSupport


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
open scoped ENNReal ContDiff Convolution
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution : HoloSmoothStatement := by
  intro n Ω f hΩ hf x₀ hx₀
  refine ContDiffAt.contDiffWithinAt ?_
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ x₀ hx₀
  set r := ε / 4 with hr
  have hr0 : 0 < r := by positivity
  have hsub : closedBall x₀ (3 * r) ⊆ Ω :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  set g := (closedBall x₀ (3 * r)).indicator f with hg
  have hgi : Integrable g := by
    rw [hg, integrable_indicator_iff measurableSet_closedBall]
    exact (hf.continuousOn.mono hsub).integrableOn_compact (isCompact_closedBall x₀ (3 * r))
  have hconv : ContDiff ℝ ∞ (mollify n r g) := by
    rw [mollify_eq_convolution]
    exact (moll_hasCompactSupport n hr0).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (moll_contDiff n r) hgi.locallyIntegrable
  have heq : f =ᶠ[𝓝 x₀] mollify n r g := by
    filter_upwards [Metric.ball_mem_nhds x₀ hr0] with x hx
    rw [Metric.mem_ball] at hx
    have hx' : closedBall x r ⊆ Ω := by
      refine (Metric.closedBall_subset_closedBall' ?_).trans hsub
      linarith
    rw [← holo_eq_mollify hr0 (hf.mono hx')]
    simp only [mollify]
    congr 1
    funext y
    by_cases hy : y ∈ closedBall x₀ (3 * r)
    · simp [hg, Set.indicator_of_mem hy]
    · have h1 : r / 2 < ‖x - y‖ := by
        rw [Metric.mem_closedBall, not_le] at hy
        have h2 := dist_triangle y x x₀
        have h3 : dist y x = ‖x - y‖ := by rw [dist_comm, dist_eq_norm]
        linarith
      simp [hg, moll_eq_zero_of_lt hr0 h1]
  exact hconv.contDiffAt.congr_of_eventuallyEq heq
end ReciprocityTheory.L2DbarEstimates.C
