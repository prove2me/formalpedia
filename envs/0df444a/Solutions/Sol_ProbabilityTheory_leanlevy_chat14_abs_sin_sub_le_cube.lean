-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat14_abs_sin_sub_le_cube
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:15:20.647268+00:00
-- url     : https://prove2.me/submissions/45e4f47c-d151-4382-b1b1-9ece29786f97

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

/-- Source Taylor bound on the complex exponential at imaginary arguments. -/
private lemma chat14_norm_exp_taylor {z : ℝ} (hz : |z| ≤ 1) :
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

/-- Cubic bound on the sine remainder, extracted from the complex exponential. -/
theorem solution {x : ℝ} (hx : |x| ≤ 1) :
    |Real.sin x - x| ≤ 2 / 9 * |x| ^ 3 := by
  have h := chat14_norm_exp_taylor hx
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
