-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.isBigO_succ_of_fderiv_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:39:27.498248+00:00
-- url     : https://prove2.me/submissions/45f57365-17ad-4b42-a720-e538024d3c7f

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_Lemmata_CharacterDirections_Cdir
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IteratedFDerivEqZeroOfIsBigO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Asymptotics Metric Set
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : V n → F} {U : Set (V n)} {x : V n} (hU : IsOpen U) (hx : x ∈ U)
    (hf : DifferentiableOn ℂ f U) (h0 : f x = 0) {m : ℕ}
    (hO : fderiv ℂ f =O[𝓝 x] fun v => ‖v - x‖ ^ m) :
    f =O[𝓝 x] fun v => ‖v - x‖ ^ (m + 1) := by
  obtain ⟨c, hc0, hc⟩ := hO.exists_pos
  rw [IsBigOWith] at hc
  obtain ⟨ε, hε0, hε⟩ := Metric.eventually_nhds_iff_ball.1 (hc.and (hU.mem_nhds hx))
  rw [isBigO_iff]
  refine ⟨c, ?_⟩
  filter_upwards [ball_mem_nhds x hε0] with v hv
  rw [norm_pow, norm_norm]
  have hvx : ‖v - x‖ < ε := by rwa [mem_ball, dist_eq_norm] at hv
  have hsub : closedBall x ‖v - x‖ ⊆ ball x ε := closedBall_subset_ball hvx
  have hmv := (convex_closedBall x ‖v - x‖).norm_image_sub_le_of_norm_fderiv_le
    (f := f) (C := c * ‖v - x‖ ^ m)
    (fun w hw => (hf w (hε _ (hsub hw)).2).differentiableAt (hU.mem_nhds (hε _ (hsub hw)).2))
    (fun w hw => by
      calc ‖fderiv ℂ f w‖ ≤ c * ‖‖w - x‖ ^ m‖ := (hε _ (hsub hw)).1
        _ = c * ‖w - x‖ ^ m := by rw [norm_pow, norm_norm]
        _ ≤ c * ‖v - x‖ ^ m := by
          gcongr
          rw [mem_closedBall, dist_eq_norm] at hw; exact hw)
    (mem_closedBall_self (norm_nonneg _)) (mem_closedBall.2 (by rw [dist_eq_norm]))
  rw [h0, sub_zero] at hmv
  calc ‖f v‖ ≤ c * ‖v - x‖ ^ m * ‖v - x‖ := hmv
    _ = c * ‖v - x‖ ^ (m + 1) := by ring
end ReciprocityTheory.L2DbarEstimates.Y
