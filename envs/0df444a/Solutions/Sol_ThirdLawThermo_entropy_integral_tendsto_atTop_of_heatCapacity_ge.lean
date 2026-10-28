-- Prove2me | solution 1 for ThirdLawThermo.entropy_integral_tendsto_atTop_of_heatCapacity_ge
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:12:40.066013+00:00
-- url     : https://prove2.me/submissions/839752ac-13fc-4b9b-8c41-cdf97f5b54ad

import Definitions.Def_ThirdLawThermo_Defs
import Mathlib

open Filter Topology
open ThirdLawThermo

namespace LUHelp

theorem log_div_tendsto (T : ℝ) (hT : 0 < T) :
    Tendsto (fun T₀ : ℝ => Real.log (T / T₀)) (𝓝[>] 0) atTop := by
  have h1 : Tendsto (fun T₀ : ℝ => Real.log T - Real.log T₀) (𝓝[>] 0) atTop := by
    have := Real.tendsto_log_nhdsGT_zero
    exact tendsto_atTop_add_const_left _ _ (tendsto_neg_atBot_atTop.comp this)
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with T₀ (h : 0 < T₀)
  rw [Real.log_div hT.ne' h.ne']

theorem integral_const_div (k T T₀ : ℝ) (hT : 0 < T) (h0 : 0 < T₀) :
    ∫ t in T₀..T, k / t = k * Real.log (T / T₀) := by
  simp_rw [div_eq_mul_inv k]
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos h0 hT]

theorem main (C : ℝ → ℝ) (c T : ℝ)
    (hc : 0 < c) (hT : 0 < T) (hC : ∀ t ∈ Set.Ioc 0 T, c ≤ C t)
    (hint : ∀ T₀ ∈ Set.Ioo 0 T,
      IntervalIntegrable (fun t => C t / t) MeasureTheory.volume T₀ T) :
    Tendsto (fun T₀ => ∫ t in T₀..T, C t / t) (𝓝[>] 0) atTop := by
  have h1 : Tendsto (fun T₀ : ℝ => c * Real.log (T / T₀)) (𝓝[>] 0) atTop :=
    (log_div_tendsto T hT).const_mul_atTop hc
  refine tendsto_atTop_mono' _ ?_ h1
  have hmem : Set.Ioo 0 T ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT hT
  filter_upwards [hmem] with T₀ hT₀
  rw [← integral_const_div c T T₀ hT hT₀.1]
  apply intervalIntegral.integral_mono_on hT₀.2.le
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro x hx
    rw [Set.uIcc_of_le hT₀.2.le] at hx
    exact (hT₀.1.trans_le hx.1).ne'
  · exact hint T₀ hT₀
  · intro x hx
    have hx0 : 0 < x := hT₀.1.trans_le hx.1
    exact div_le_div_of_nonneg_right (hC x ⟨hx0, hx.2⟩) hx0.le

end LUHelp
theorem solution (C : ℝ → ℝ) (c T : ℝ)
    (hc : 0 < c) (hT : 0 < T) (hC : ∀ t ∈ Set.Ioc 0 T, c ≤ C t)
    (hint : ∀ T₀ ∈ Set.Ioo 0 T,
      IntervalIntegrable (fun t => C t / t) MeasureTheory.volume T₀ T) :
    Tendsto (fun T₀ => ∫ t in T₀..T, C t / t) (𝓝[>] 0) atTop :=
  LUHelp.main C c T hc hT hC hint
