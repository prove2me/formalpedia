-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.vanish_lintegral_ball_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:25:58.334812+00:00
-- url     : https://prove2.me/submissions/77250102-5323-4383-9872-8157a644f4ec

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_Vanish

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (n : ℕ) (F : V n → ℝ≥0∞) (hF : Measurable F) {ρ : ℝ}
    (hρ : 0 < ρ) :
    ∫⁻ y in ball (0 : V n) 1, F (ρ • y) =
      ENNReal.ofReal |(ρ ^ Module.finrank ℝ (V n))⁻¹| * ∫⁻ y in ball (0 : V n) ρ, F y := by
  have hind : ∀ y : V n, (ball (0 : V n) 1).indicator (fun y => F (ρ • y)) y =
      (ball (0 : V n) ρ).indicator F (ρ • y) := by
    intro y
    have hm : ρ • y ∈ ball (0 : V n) ρ ↔ y ∈ ball (0 : V n) 1 := by
      simp only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
      exact mul_lt_iff_lt_one_right hρ
    by_cases h : y ∈ ball (0 : V n) 1
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hm.mpr h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hm.mp h'))]
  rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball]
  simp_rw [hind]
  have hFm : Measurable ((ball (0 : V n) ρ).indicator F) := hF.indicator measurableSet_ball
  rw [← lintegral_map hFm (measurable_const_smul ρ), Measure.map_addHaar_smul _ hρ.ne',
    lintegral_smul_measure, smul_eq_mul]
end ReciprocityTheory.L2DbarEstimates.I
