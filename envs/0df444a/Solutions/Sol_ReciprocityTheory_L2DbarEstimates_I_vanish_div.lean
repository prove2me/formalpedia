-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.vanish_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:43:17.3942+00:00
-- url     : https://prove2.me/submissions/89448354-463e-41c4-8d62-111afae91439

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_Vanish
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_vanish_lintegral_ball_smul

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
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) (hDiv : C.MVDivStatement) {ρ c : ℝ} (hρ : 0 < ρ)
    (hc : 0 < c) {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝[>] 0)) :
    Tendsto (fun k => ∫⁻ y in ball (0 : V n) ρ,
      ENNReal.ofReal ((c * ‖y‖ ^ 2 + δ k) ^ (-(n : ℝ)))) atTop (𝓝 ∞) := by
  have hn0 : 0 < n := hn
  have hcr : 0 < c * ρ ^ 2 := by positivity
  obtain ⟨hδ0, hδpos⟩ := tendsto_nhdsWithin_iff.mp hδ
  have hη : Tendsto (fun k => δ k / (c * ρ ^ 2)) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using hδ0.div_const (c * ρ ^ 2)
    · exact hδpos.mono fun k hk => div_pos hk hcr
  have hΦ := (hDiv n hn0).comp hη
  set K : ℝ≥0∞ := ENNReal.ofReal (ρ ^ Module.finrank ℝ (V n)) *
    ENNReal.ofReal ((c * ρ ^ 2) ^ (-(n : ℝ))) with hK
  have hK0 : K ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr (by positivity)).ne' (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hlim := ENNReal.Tendsto.const_mul (a := K) hΦ (Or.inl ENNReal.top_ne_zero)
  rw [ENNReal.mul_top hK0] at hlim
  refine hlim.congr' ?_
  filter_upwards [hδpos] with k hk
  have hk' : 0 < δ k := hk
  have hG : Measurable fun y : V n => ENNReal.ofReal ((c * ‖y‖ ^ 2 + δ k) ^ (-(n : ℝ))) := by
    fun_prop
  have hs := vanish_lintegral_ball_smul n _ hG hρ
  have hd : ENNReal.ofReal (ρ ^ Module.finrank ℝ (V n)) *
      ENNReal.ofReal |(ρ ^ Module.finrank ℝ (V n))⁻¹| = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity),
      mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one]
  have hrhs : ∫⁻ y in ball (0 : V n) ρ, ENNReal.ofReal ((c * ‖y‖ ^ 2 + δ k) ^ (-(n : ℝ))) =
      ENNReal.ofReal (ρ ^ Module.finrank ℝ (V n)) *
        ∫⁻ y in ball (0 : V n) 1, ENNReal.ofReal ((c * ‖ρ • y‖ ^ 2 + δ k) ^ (-(n : ℝ))) := by
    rw [hs, ← mul_assoc, hd, one_mul]
  show K * _ = _
  rw [hrhs, hK, mul_assoc]
  congr 1
  simp only [Function.comp_apply]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr (fun z => ?_)
  have hz : 0 ≤ ‖z‖ ^ 2 + δ k / (c * ρ ^ 2) := by positivity
  rw [← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow hcr.le hz]
  congr 2
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
  field_simp
end ReciprocityTheory.L2DbarEstimates.I
