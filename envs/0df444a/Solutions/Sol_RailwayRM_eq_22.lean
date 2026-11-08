-- Prove2me | solution 1 for RailwayRM.eq_22
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:33:41.851795+00:00
-- url     : https://prove2.me/submissions/43b7a1d7-5e4e-43f5-b074-804bc48e89b0

import Mathlib

open MeasureTheory ProbabilityTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : MemLp W 2 P) (a : ℝ) :
    ∫ ω, max (W ω - a) 0 ∂P ≤ Real.sqrt (variance W P) / 2 + max ((∫ ω, W ω ∂P) - a) 0 := by
  set μ := ∫ ω, W ω ∂P with hμ
  have hWi : Integrable W P := hW.integrable one_le_two
  have hYm : MemLp (fun ω => W ω - a) 2 P := hW.sub (memLp_const a)
  have hYi : Integrable (fun ω => W ω - a) P := hYm.integrable one_le_two
  have hAm : MemLp (fun ω => |W ω - a|) 2 P := hYm.abs
  have hAi : Integrable (fun ω => |W ω - a|) P := hAm.integrable one_le_two
  -- ∫ max = ((μ - a) + E|W - a|)/2
  have hmax : ∀ x : ℝ, max x 0 = (x + |x|) / 2 := by
    intro x
    rcases le_total 0 x with h | h
    · rw [max_eq_left h, abs_of_nonneg h]; ring
    · rw [max_eq_right h, abs_of_nonpos h]; ring
  have h1 : ∫ ω, max (W ω - a) 0 ∂P = ((μ - a) + ∫ ω, |W ω - a| ∂P) / 2 := by
    simp_rw [hmax]
    rw [integral_div, integral_add hYi hAi, integral_sub hWi (integrable_const a), integral_const,
      probReal_univ, one_smul]
  -- second moment of W - a
  have hsq : ∫ ω, (W ω - a) ^ 2 ∂P = variance W P + (μ - a) ^ 2 := by
    rw [variance_eq_sub hW]
    have hW2 : Integrable (fun ω => W ω ^ 2) P := hW.integrable_sq
    have e : ∀ ω, (W ω - a) ^ 2 = W ω ^ 2 - 2 * a * W ω + a ^ 2 := fun ω => by ring
    simp_rw [e]
    have i1 : Integrable (fun ω => W ω ^ 2 - 2 * a * W ω) P := hW2.sub (hWi.const_mul _)
    rw [integral_add i1 (integrable_const _), integral_sub hW2 (hWi.const_mul _),
      integral_const_mul, integral_const, probReal_univ, one_smul]
    simp only [Pi.pow_apply]
    rw [← hμ]
    ring
  -- Jensen for |W - a|
  have hjen : (∫ ω, |W ω - a| ∂P) ^ 2 ≤ ∫ ω, (W ω - a) ^ 2 ∂P := by
    have hv := variance_nonneg (fun ω => |W ω - a|) P
    rw [variance_eq_sub hAm] at hv
    have : ∫ ω, ((fun ω => |W ω - a|) ^ 2) ω ∂P = ∫ ω, (W ω - a) ^ 2 ∂P := by
      congr 1; funext ω; simp [sq_abs]
    rw [this] at hv
    linarith
  set σ := Real.sqrt (variance W P) with hσ
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσ2 : σ ^ 2 = variance W P := Real.sq_sqrt (variance_nonneg W P)
  have hE0 : 0 ≤ ∫ ω, |W ω - a| ∂P := integral_nonneg (fun ω => abs_nonneg _)
  have hEbound : ∫ ω, |W ω - a| ∂P ≤ σ + |μ - a| := by
    have h2 : (∫ ω, |W ω - a| ∂P) ^ 2 ≤ (σ + |μ - a|) ^ 2 := by
      calc (∫ ω, |W ω - a| ∂P) ^ 2 ≤ variance W P + (μ - a) ^ 2 := hsq ▸ hjen
        _ ≤ (σ + |μ - a|) ^ 2 := by
          rw [← hσ2, add_sq, sq_abs]
          have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hσ0) (abs_nonneg (μ - a))
          linarith
    exact (pow_le_pow_iff_left₀ hE0 (by positivity) (by norm_num)).1 h2
  rw [h1, hmax (μ - a)]
  linarith
