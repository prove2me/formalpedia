-- Prove2me | solution 1 for ThirdLawThermo.powerLaw_heatCapacity_entropy_bounded_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:13:13.063126+00:00
-- url     : https://prove2.me/submissions/de67f027-70cd-40b7-82d8-28e6ed0dc0f7

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
theorem solution (C₀ α T : ℝ) (hC₀ : 0 < C₀) (hT : 0 < T) :
    (∃ M : ℝ, ∀ T₀ ∈ Set.Ioo 0 T, ∫ t in T₀..T, C₀ * t ^ α / t ≤ M) ↔ 0 < α := by
  constructor
  · rintro ⟨M, hM⟩
    by_contra hα
    push_neg at hα
    have hint : ∀ T₀ ∈ Set.Ioo 0 T,
        IntervalIntegrable (fun t => C₀ * t ^ α / t) MeasureTheory.volume T₀ T := by
      intro T₀ hT₀
      apply ContinuousOn.intervalIntegrable
      intro x hx
      rw [Set.uIcc_of_le hT₀.2.le] at hx
      have hx0 : 0 < x := hT₀.1.trans_le hx.1
      apply ContinuousAt.continuousWithinAt
      apply ContinuousAt.div _ continuousAt_id hx0.ne'
      exact continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl hx0.ne'))
    have h := LUHelp.main (fun t => C₀ * t ^ α) (C₀ * T ^ α) T (by positivity) hT
      (fun t ht => mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos ht.1 ht.2 hα) hC₀.le) hint
    obtain ⟨T₀, h1, h2⟩ :=
      ((h.eventually (eventually_gt_atTop M)).and (Ioo_mem_nhdsGT hT)).exists
    exact absurd (hM T₀ h2) (not_le.2 h1)
  · intro hα
    refine ⟨C₀ * (T ^ α / α), fun T₀ hT₀ => ?_⟩
    have hcongr : ∫ t in T₀..T, C₀ * t ^ α / t = ∫ t in T₀..T, C₀ * t ^ (α - 1) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hT₀.2.le] at hx
      have hx0 : 0 < x := hT₀.1.trans_le hx.1
      simp only
      rw [Real.rpow_sub_one hx0.ne', mul_div_assoc]
    rw [hcongr, intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
    apply mul_le_mul_of_nonneg_left _ hC₀.le
    rw [sub_add_cancel]
    apply div_le_div_of_nonneg_right _ hα.le
    have := Real.rpow_pos_of_pos hT₀.1 α
    linarith
