-- Prove2me | solution 1 for SumProduct.integrable_sinc_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:51:37.663903+00:00
-- url     : https://prove2.me/submissions/ebe31602-4d82-48d5-a039-a75c06e71e5f

import Mathlib
import Definitions.Def_SumProduct_SincIntegral
section
open MeasureTheory Set
namespace SumProduct
open Real
private lemma abs_sinc_le_inv_abs {t : ℝ} (ht : t ≠ 0) :
    |Real.sinc t| ≤ |t|⁻¹ := by
  rw [Real.sinc_of_ne_zero ht, abs_div]
  rw [div_le_iff₀ (by positivity)]
  rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
  calc |Real.sin t| * |t| ≤ 1 * |t| := by
        gcongr; exact abs_sin_le_one t
    _ = |t| := by ring
private lemma abs_sinc_pow_le {t : ℝ} (ht : t ≠ 0) (N : ℕ) :
    |Real.sinc t| ^ N ≤ (|t|⁻¹) ^ N := by
  apply pow_le_pow_left₀ (abs_nonneg _) (abs_sinc_le_inv_abs ht)
private lemma abs_sinc_pow_le_inv_sq {t : ℝ} (ht : 1 ≤ |t|) {N : ℕ} (hN : 2 ≤ N) :
    |Real.sinc t| ^ N ≤ (|t| ^ 2)⁻¹ := by
  have ht0 : t ≠ 0 := by
    intro h; rw [h] at ht; simp at ht; linarith
  calc |Real.sinc t| ^ N ≤ (|t|⁻¹) ^ N := abs_sinc_pow_le ht0 N
    _ ≤ (|t|⁻¹) ^ 2 := by
        apply pow_le_pow_of_le_one (by positivity)
        · rw [inv_le_one_iff₀]; right; exact ht
        · exact hN
    _ = (|t| ^ 2)⁻¹ := by rw [inv_pow]
private lemma abs_sinc_pow_le_dom (t : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    |Real.sinc t| ^ N ≤ 2 * (1 + t ^ 2)⁻¹ := by
  rcases le_or_gt 1 |t| with ht | ht
  · have h1 : |Real.sinc t| ^ N ≤ (|t| ^ 2)⁻¹ := abs_sinc_pow_le_inv_sq ht hN
    have htsq : (1 : ℝ) ≤ t ^ 2 := by nlinarith [sq_abs t, ht, abs_nonneg t]
    have h2 : (|t| ^ 2)⁻¹ ≤ 2 * (1 + t ^ 2)⁻¹ := by
      rw [sq_abs]
      have hp1 : (0:ℝ) < t ^ 2 := by linarith
      have hp2 : (0:ℝ) < 1 + t ^ 2 := by linarith
      have e1 : (t ^ 2)⁻¹ = 1 / t ^ 2 := by rw [one_div]
      have e2 : (1 + t ^ 2)⁻¹ = 1 / (1 + t ^ 2) := by rw [one_div]
      rw [e1, e2, mul_one_div, div_le_div_iff₀ hp1 hp2]
      nlinarith [htsq]
    exact h1.trans h2
  · have hb : |Real.sinc t| ^ N ≤ 1 := by
      apply pow_le_one₀ (abs_nonneg _) (Real.abs_sinc_le_one t)
    have h2 : (1 : ℝ) ≤ 2 * (1 + t ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ (by positivity)]
      nlinarith [sq_abs t, ht, abs_nonneg t]
    exact hb.trans h2
end SumProduct
end

set_option autoImplicit true
open MeasureTheory Set
open SumProduct
open Real
namespace SumProduct
theorem _root_.solution {N : ℕ} (hN : 2 ≤ N) :
    Integrable (fun t : ℝ => (Real.sinc t) ^ N) := by
  apply Integrable.mono' (g := fun t => 2 * (1 + t ^ 2)⁻¹)
    (integrable_inv_one_add_sq.const_mul 2)
  · exact (Real.continuous_sinc.pow N).aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_pow]
    exact abs_sinc_pow_le_dom t hN
end SumProduct
