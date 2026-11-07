-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat15_one_sub_sinc_le_mul_min_inline
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:22:11.698278+00:00
-- url     : https://prove2.me/submissions/7b1f1233-e174-4831-a91b-f295f33596b2

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

/-- Cubic Taylor control for the complex exponential on imaginary arguments. -/
private lemma chat15_norm_exp_taylor {z : ℝ} (hz : |z| ≤ 1) :
    ‖Complex.exp ((↑z : ℂ) * I) - 1 - (↑z : ℂ) * I + (↑z : ℂ) ^ 2 / 2‖ ≤
      (2 / 9 : ℝ) * |z| ^ 3 := by
  set w : ℂ := (↑z : ℂ) * I with hw_def
  have hw_norm : ‖w‖ ≤ 1 := by
    rw [hw_def, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hz
  have hbound := Complex.exp_bound hw_norm (n := 3) (by decide)
  have hsum : ∑ m ∈ Finset.range 3, w ^ m / (m.factorial : ℂ) = 1 + w + w ^ 2 / 2 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_one]
    simp [Nat.factorial]
  rw [hsum] at hbound
  have hw_sq : w ^ 2 = -((↑z : ℂ) ^ 2) := by
    rw [hw_def, mul_pow, Complex.I_sq]; ring
  have hLHS : ‖Complex.exp w - (1 + w + w ^ 2 / 2)‖ =
      ‖Complex.exp w - 1 - w + (↑z : ℂ) ^ 2 / 2‖ := by
    congr 1; rw [hw_sq]; ring
  rw [hLHS] at hbound
  have hw_pow : ‖w‖ ^ 3 = |z| ^ 3 := by
    rw [hw_def, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  calc ‖Complex.exp w - 1 - w + (↑z : ℂ) ^ 2 / 2‖
      ≤ ‖w‖ ^ 3 * ((Nat.succ 3 : ℝ) * ((3 : ℕ).factorial * 3 : ℝ)⁻¹) := hbound
    _ = |z| ^ 3 * (4 / 18) := by rw [hw_pow]; norm_num [Nat.factorial]
    _ = (2 / 9 : ℝ) * |z| ^ 3 := by ring

/-- Sine remainder from the imaginary part of the exponential. -/
private lemma chat15_abs_sin_cube {x : ℝ} (hx : |x| ≤ 1) :
    |Real.sin x - x| ≤ 2 / 9 * |x| ^ 3 := by
  have h := chat15_norm_exp_taylor hx
  have him : (Complex.exp ((↑x : ℂ) * I) - 1 - (↑x : ℂ) * I + (↑x : ℂ) ^ 2 / 2).im
      = Real.sin x - x := by
    have hcast : (↑x : ℂ) ^ 2 / 2 = ((x ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast]
    simp only [Complex.add_im, Complex.sub_im, Complex.exp_ofReal_mul_I_im, Complex.one_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  calc |Real.sin x - x|
      = |(Complex.exp ((↑x : ℂ) * I) - 1 - (↑x : ℂ) * I + (↑x : ℂ) ^ 2 / 2).im| := by rw [him]
    _ ≤ ‖Complex.exp ((↑x : ℂ) * I) - 1 - (↑x : ℂ) * I + (↑x : ℂ) ^ 2 / 2‖ :=
        Complex.abs_im_le_norm _
    _ ≤ 2 / 9 * |x| ^ 3 := h

/-- Source upper sinc bound, self-contained under the pinned Mathlib import. -/
theorem solution : ∀ (x : ℝ), 1 - Real.sinc x ≤ 2 * min 1 (x ^ 2) := by
  intro x
  have hsinc : Real.sinc x = Real.sinc |x| := by
    rcases abs_choice x with h | h <;> simp [h, Real.sinc_neg]
  rw [hsinc, show x ^ 2 = |x| ^ 2 from (sq_abs x).symm]
  set y := |x| with hy
  have hy0 : 0 ≤ y := abs_nonneg x
  rcases le_or_gt (y ^ 2) 1 with hy1 | hy1
  · rw [min_eq_right hy1]
    by_cases hy00 : y = 0
    · rw [hy00]; simp
    · have hypos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hy00)
      have hyle1 : y ≤ 1 := by nlinarith [hy1, hy0]
      rw [Real.sinc_of_ne_zero hypos.ne']
      have hcube := chat15_abs_sin_cube (x := y)
        (by rw [abs_of_nonneg hy0]; exact hyle1)
      rw [abs_of_nonneg hy0] at hcube
      have hydiff : y - Real.sin y ≤ 2 / 9 * y ^ 3 := by
        have := (abs_le.mp hcube).1
        linarith
      have hkey : 1 - Real.sin y / y ≤ 2 / 9 * y ^ 2 := by
        rw [show (1 : ℝ) - Real.sin y / y = (y - Real.sin y) / y from by field_simp,
            div_le_iff₀ hypos]
        nlinarith [hydiff]
      nlinarith [hkey, sq_nonneg y]
  · rw [min_eq_left hy1.le]
    have := Real.neg_one_le_sinc y
    linarith
