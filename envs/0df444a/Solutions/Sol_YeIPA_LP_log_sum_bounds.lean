-- Prove2me | solution 1 for YeIPA.LP.log_sum_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:02:14.440912+00:00
-- url     : https://prove2.me/submissions/8be5e9fd-2570-4e67-94cf-9373420807f0

import Mathlib
import Definitions.Def_YeIPA_LP_PotentialReduction

open Matrix
open YeIPA.LP
theorem g69c_log_term {d r : ℝ} (hd : |d| ≤ r) (hr : r < 1) :
    d - d ^ 2 / (2 * (1 - r)) ≤ Real.log (1 + d) := by
  have hr0 : 0 ≤ r := le_trans (abs_nonneg _) hd
  have h1r : 0 < 1 - r := by linarith
  rcases le_total 0 d with h | h
  · -- x = d/(2+d)
    set x := d / (2 + d) with hx
    have hx0 : 0 ≤ x := by positivity
    have hx1 : x < 1 := by rw [hx, div_lt_one (by linarith)]; linarith
    have key := Real.sum_range_le_log_div hx0 hx1 1
    simp only [Finset.sum_range_one, mul_zero, zero_add, pow_one, Nat.cast_zero] at key
    have he : (1 + x) / (1 - x) = 1 + d := by
      rw [hx]; field_simp; ring
    rw [he] at key
    have hsq : d - d ^ 2 / (2 * (1 - r)) ≤ d - d ^ 2 / 2 := by
      have : d ^ 2 / 2 ≤ d ^ 2 / (2 * (1 - r)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity); nlinarith
      linarith
    have h2 : d - d ^ 2 / 2 ≤ 2 * x := by
      rw [hx]; rw [show 2 * (d / (2 + d)) = 2 * d / (2 + d) by ring, le_div_iff₀ (by linarith)]
      nlinarith [sq_nonneg d, mul_nonneg h (sq_nonneg d)]
    linarith
  · have hd' : -d ≤ r := by rw [abs_of_nonpos h] at hd; exact hd
    have hu : 0 < 1 + d := by linarith
    set u := 1 + d with hu'
    have hu0 : u ≠ 0 := hu.ne'
    have hu1 : 1 + u ≠ 0 := by linarith
    set x := (1 - u) / (1 + u) with hx
    have hx0 : 0 ≤ x := by apply div_nonneg <;> linarith
    have hx1 : x < 1 := by rw [hx, div_lt_one (by linarith)]; linarith
    have key := Real.log_div_le_sum_range_add hx0 hx1 0
    clear_value x u
    simp only [Finset.range_zero, Finset.sum_empty, zero_add, mul_zero, pow_one] at key
    have h1x : 1 - x ≠ 0 := by linarith
    have h1x2 : 1 - x ^ 2 ≠ 0 := by nlinarith
    have he : (1 + x) / (1 - x) = u⁻¹ := by
      rw [div_eq_iff h1x, hx]; field_simp; ring
    have he2 : x / (1 - x ^ 2) = (u⁻¹ - u) / 4 := by
      rw [div_eq_iff h1x2, hx]; field_simp; ring
    rw [he, he2, Real.log_inv] at key
    have h3 : d - d ^ 2 / (2 * (1 - r)) ≤ d - d ^ 2 / (2 * u) := by
      have : d ^ 2 / (2 * u) ≤ d ^ 2 / (2 * (1 - r)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity); linarith
      linarith
    have h4 : d - d ^ 2 / (2 * u) = - (2 * ((u⁻¹ - u) / 4)) := by
      have : (1 + d) ≠ 0 := by linarith
      rw [hu']; field_simp; ring
    linarith

theorem g69c_log_sum {n : ℕ} (d : Fin n → ℝ) (hd : (⨆ j, |d j|) < 1) :
    ∑ i, Real.log (1 + d i) ≤ ∑ i, d i ∧
      ∑ i, d i - Real.sqrt (∑ j, d j ^ 2) ^ 2 / (2 * (1 - ⨆ j, |d j|)) ≤
        ∑ i, Real.log (1 + d i) := by
  have hle : ∀ i, |d i| ≤ ⨆ j, |d j| := fun i => le_ciSup (f := fun j => |d j|) (Finite.bddAbove_range _) i
  constructor
  · apply Finset.sum_le_sum
    intro i _
    have h1 : 0 < 1 + d i := by
      have := hle i; have := neg_abs_le (d i); linarith
    have := Real.log_le_sub_one_of_pos h1
    linarith
  · rw [Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg (d j))), Finset.sum_div,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun i _ => g69c_log_term (hle i) hd)


/-- Lemma 3.1 (Ye 1997, p. 84), restated for Chapter 4. If `d ∈ ℝⁿ` with `‖d‖_∞ < 1`, then
`eᵀd ≥ ∑ᵢ log(1 + dᵢ) ≥ eᵀd − ‖d‖² / (2(1 − ‖d‖_∞))`. -/
theorem solution {n : ℕ} (d : Fin n → ℝ) (hd : normInf d < 1) :
    ∑ i, Real.log (1 + d i) ≤ ∑ i, d i ∧
      ∑ i, d i - norm2 d ^ 2 / (2 * (1 - normInf d)) ≤ ∑ i, Real.log (1 + d i) := by
  have h := g69c_log_sum d hd
  exact h


