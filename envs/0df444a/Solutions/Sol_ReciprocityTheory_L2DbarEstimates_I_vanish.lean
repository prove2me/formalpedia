-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:30:19.469306+00:00
-- url     : https://prove2.me/submissions/8aba2527-56c6-4319-8eb3-d1a25bbd8be1

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_Vanish
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_vanish_div

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
theorem _root_.solution (n : ℕ) (hMV : C.MVStatement) (hDiv : C.MVDivStatement) : VanishStatement n := by
  intro hn ρ c C0 δ u hρ hc hδ hu hb
  have hW := vanish_div n hn hDiv hρ hc hδ
  set W : ℕ → ℝ≥0∞ := fun k => ∫⁻ y in ball (0 : V n) ρ,
    ENNReal.ofReal ((c * ‖y‖ ^ 2 + δ k) ^ (-(n : ℝ))) with hWdef
  have hmv : ∀ k, ‖u k 0‖ₑ ^ 2 * W k ≤ ENNReal.ofReal C0 := by
    intro k
    have hr : Measurable fun t : ℝ => ENNReal.ofReal ((c * t ^ 2 + δ k) ^ (-(n : ℝ))) := by
      fun_prop
    have h1 := hMV n 0 ρ (u k) _ (hu k) hr
    simp only [sub_zero] at h1
    refine le_trans h1 (le_trans (le_of_eq ?_) (hb k))
    refine lintegral_congr (fun y => ?_)
    rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hbd : ∀ᶠ k in atTop, ‖u k 0‖ₑ ^ 2 ≤ ENNReal.ofReal C0 / W k := by
    filter_upwards [hW.eventually (lt_mem_nhds ENNReal.one_lt_top)] with k hk
    rw [ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt (lt_trans zero_lt_one hk)))
      (Or.inr ENNReal.ofReal_ne_top)]
    exact hmv k
  have hq : Tendsto (fun k => ENNReal.ofReal C0 / W k) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_div (a := ENNReal.ofReal C0) hW (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  have hsq : Tendsto (fun k => ‖u k 0‖ₑ ^ 2) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hq
      (Filter.Eventually.of_forall fun _ => bot_le) hbd
  have hr : Tendsto (fun k => ‖u k 0‖ ^ 2) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsq
    simpa [Function.comp_def, ENNReal.toReal_pow] using this
  have hn' : Tendsto (fun k => ‖u k 0‖) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hr
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn'
end ReciprocityTheory.L2DbarEstimates.I
