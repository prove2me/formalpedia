-- Prove2me | solution 1 for UnphysicalHilbert.eq27_28_moments
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:48:06.384687+00:00
-- url     : https://prove2.me/submissions/17e6a1e4-94c3-405f-9811-fb062836d4af

import Mathlib
import Definitions.Def_UnphysicalHilbert_Position

open MeasureTheory Real UnphysicalHilbert

lemma gw_sq (x : ℝ) : gaussianWave x ^ 2 = exp (-x ^ 2) / √π := by
  unfold gaussianWave
  rw [sq_sqrt (by positivity)]

lemma lw_sq (y : ℝ) : lorentzianWave y ^ 2 = π⁻¹ * (1 + y ^ 2)⁻¹ := by
  unfold lorentzianWave
  rw [div_pow, sq_sqrt (by positivity)]
  field_simp
  ring

theorem solution :
    ∫ x, gaussianWave x ^ 2 = 1 ∧ ∫ y, lorentzianWave y ^ 2 = 1 ∧
    (∀ n : ℕ, Integrable (fun x : ℝ => |x| ^ n * gaussianWave x ^ 2)) ∧
    (∀ n : ℕ, 2 ≤ n → ¬ Integrable (fun y : ℝ => |y| ^ n * lorentzianWave y ^ 2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp_rw [gw_sq]
    rw [integral_div]
    have := integral_gaussian 1
    simp only [neg_mul, one_mul, div_one] at this
    rw [this]
    exact div_self (sqrt_pos.mpr pi_pos).ne'
  · simp_rw [lw_sq]
    rw [integral_const_mul, integral_univ_inv_one_add_sq, inv_mul_cancel₀ pi_pos.ne']
  · intro n
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos
      (s := ((n : ℕ) : ℝ)) (by have := n.cast_nonneg (α := ℝ); linarith)
    simp_rw [rpow_natCast] at h
    have h2 := (h.abs).div_const (√π)
    refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [gw_sq, abs_mul, abs_pow, abs_of_pos (exp_pos _)]
    ring_nf
  · intro n hn hint
    have h1 : IntegrableOn (fun y : ℝ => |y| ^ n * lorentzianWave y ^ 2) (Set.Ioi 1) :=
      hint.integrableOn
    have h2 : IntegrableOn (fun _ : ℝ => (2 * π)⁻¹) (Set.Ioi 1) := by
      refine h1.mono' (by fun_prop) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hy1 : (1:ℝ) < y := hy
      rw [Real.norm_eq_abs, abs_of_pos (by positivity), lw_sq, abs_of_pos (by linarith)]
      have hyn : y ^ 2 ≤ y ^ n := pow_le_pow_right₀ hy1.le hn
      have hp := pi_pos
      rw [show (2 * π)⁻¹ = π⁻¹ * (1 + y ^ 2)⁻¹ * ((1 + y ^ 2) / 2) by field_simp]
      rw [show y ^ n * (π⁻¹ * (1 + y ^ 2)⁻¹) = π⁻¹ * (1 + y ^ 2)⁻¹ * y ^ n by ring]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    rw [integrableOn_const_iff] at h2
    rcases h2 with h2 | h2
    · have : (2 * π)⁻¹ ≠ 0 := by positivity
      exact this (enorm_eq_zero.mp h2)
    · simp at h2
