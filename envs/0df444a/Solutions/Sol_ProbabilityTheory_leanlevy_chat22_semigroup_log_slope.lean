-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat22_semigroup_log_slope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:09:19.901643+00:00
-- url     : https://prove2.me/submissions/16a946b5-9692-4654-9bbb-f6121ce01ab2

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped NNReal

/-- The sixth phase of LeanLevy's original factorisation argument: the
principal-logarithm slope at time zero recovers the exponential coefficient. -/
theorem solution (φ : ℝ≥0 → ℂ) (c : ℂ)
    (hext : ∀ t : ℝ≥0, φ t = exp (c * ↑(t : ℝ))) :
    Filter.limUnder (𝓝[>] (0 : ℝ≥0))
      (fun t : ℝ≥0 => log (φ t) / ↑(t : ℝ)) = c := by
  apply Filter.Tendsto.limUnder_eq
  set δ₂ : ℝ≥0 := ⟨Real.pi / (|c.im| + 1), by positivity⟩
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ≥0) < δ₂ from by
      change (0 : ℝ) < Real.pi / (|c.im| + 1)
      positivity))]
    with t (ht_pos : 0 < t) (ht_small : t < δ₂)
  symm
  change log (φ t) / ↑↑t = c
  have ht_real_pos : (0 : ℝ) < (t : ℝ) := by
    exact_mod_cast ht_pos
  rw [hext t]
  have him : (c * ↑(t : ℝ)).im = c.im * (t : ℝ) := by
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  have him_bound : |c.im * (t : ℝ)| < Real.pi := by
    by_cases hc : c.im = 0
    · simp [hc, Real.pi_pos]
    · have ht_lt : (t : ℝ) < Real.pi / (|c.im| + 1) := by
        exact_mod_cast ht_small
      calc |c.im * (t : ℝ)|
          = |c.im| * (t : ℝ) := by rw [abs_mul, abs_of_nonneg ht_real_pos.le]
        _ < |c.im| * (Real.pi / (|c.im| + 1)) :=
          mul_lt_mul_of_pos_left ht_lt (abs_pos.mpr hc)
        _ ≤ Real.pi := by
          have hne : |c.im| + 1 ≠ 0 := by
            linarith [abs_nonneg c.im]
          calc |c.im| * (Real.pi / (|c.im| + 1))
              ≤ (|c.im| + 1) * (Real.pi / (|c.im| + 1)) :=
                mul_le_mul_of_nonneg_right
                  (le_add_of_nonneg_right zero_le_one)
                  (div_nonneg Real.pi_pos.le
                    (by linarith [abs_nonneg c.im]))
            _ = Real.pi := mul_div_cancel₀ Real.pi hne
  rw [log_exp (by rw [him]; linarith [(abs_lt.mp him_bound).1])
              (by rw [him]; linarith [(abs_lt.mp him_bound).2]),
      mul_div_cancel_right₀ c
        (by exact_mod_cast ne_of_gt ht_real_pos : (↑(t : ℝ) : ℂ) ≠ 0)]
