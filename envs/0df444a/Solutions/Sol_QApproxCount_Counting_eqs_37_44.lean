-- Prove2me | solution 1 for QApproxCount.Counting.eqs_37_44
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:44:10.156133+00:00
-- url     : https://prove2.me/submissions/45ddc171-0c50-4816-a4c0-a5c628155595

import Mathlib
set_option autoImplicit false

lemma aux_arith_geom (b : ℝ) (n : ℕ) :
    (∑ t ∈ Finset.range n, b ^ t * ((n : ℝ) - t)) * (b - 1) ^ 2
      = b ^ (n + 1) - b - n * (b - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ∑ t ∈ Finset.range (n + 1), b ^ t * (((n + 1 : ℕ) : ℝ) - t)
        = (∑ t ∈ Finset.range n, b ^ t * ((n : ℝ) - t)) + ∑ t ∈ Finset.range (n + 1), b ^ t := by
      have : ∀ t ∈ Finset.range (n + 1),
          b ^ t * (((n + 1 : ℕ) : ℝ) - t) = b ^ t * ((n : ℝ) - t) + b ^ t := by
        intro t _; push_cast; ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_range_succ _ n]
      simp
    have h2 : (∑ t ∈ Finset.range (n + 1), b ^ t) * (b - 1) = b ^ (n + 1) - 1 :=
      geom_sum_mul b (n + 1)
    rw [h1, add_mul, ih]
    have : (∑ t ∈ Finset.range (n + 1), b ^ t) * (b - 1) ^ 2
        = (∑ t ∈ Finset.range (n + 1), b ^ t) * (b - 1) * (b - 1) := by ring
    rw [this, h2]
    push_cast
    ring

theorem solution (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (T : ℕ)
    (hT : Real.log (1 / ε) ≤ Real.log (1 / 0.9) * ((T : ℝ) + 1))
    (hTupper : ε / 5 ≤ 0.65 * (0.9 : ℝ) ^ T) :
    ∑ t ∈ Finset.range (T + 1),
        (1 / 0.9 : ℝ) ^ t * (Real.log (1 / ε) - (t : ℝ) * Real.log (1 / 0.9)) ≤
      Real.log (1 / 0.9) * (1 / 0.9 : ℝ) ^ (T + 2) / (1 / 0.9 - 1) ^ 2 ∧
    Real.log (1 / 0.9) * (1 / 0.9 : ℝ) ^ (T + 2) / (1 / 0.9 - 1) ^ 2 ≤
      (Real.log (1 / 0.9) * (1 / 0.9 : ℝ) ^ 2 * 3.25 / (1 / 0.9 - 1) ^ 2) / ε := by
  set b : ℝ := 1 / 0.9 with hb
  have hb1 : 1 < b := by rw [hb]; norm_num
  have hb0 : 0 < b := by linarith
  set L : ℝ := Real.log b with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hb1.le
  have hbm : 0 < (b - 1) ^ 2 := by have : 0 < b - 1 := by linarith
                                   positivity
  have hT' : Real.log (1 / ε) ≤ L * ((T : ℝ) + 1) := hT
  constructor
  · -- termwise bound
    have hterm : ∀ t ∈ Finset.range (T + 1),
        b ^ t * (Real.log (1 / ε) - (t : ℝ) * L) ≤ L * (b ^ t * (((T + 1 : ℕ) : ℝ) - t)) := by
      intro t _
      have : Real.log (1 / ε) - (t : ℝ) * L ≤ L * (((T + 1 : ℕ) : ℝ) - t) := by
        push_cast; nlinarith
      calc b ^ t * (Real.log (1 / ε) - (t : ℝ) * L)
          ≤ b ^ t * (L * (((T + 1 : ℕ) : ℝ) - t)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have hsum := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum] at hsum
    have haux := aux_arith_geom b (T + 1)
    have hS : (∑ t ∈ Finset.range (T + 1), b ^ t * (((T + 1 : ℕ) : ℝ) - t)) ≤
        b ^ (T + 2) / (b - 1) ^ 2 := by
      rw [le_div_iff₀ hbm, haux]
      have : ((T + 1 : ℕ) : ℝ) * (b - 1) ≥ 0 := by
        have : 0 < b - 1 := by linarith
        positivity
      nlinarith
    calc _ ≤ _ := hsum
      _ ≤ L * (b ^ (T + 2) / (b - 1) ^ 2) := mul_le_mul_of_nonneg_left hS hL0
      _ = _ := by ring
  · -- second bound
    have h09 : (0 : ℝ) < 0.9 ^ T := by positivity
    have hbT : b ^ T * (0.9 : ℝ) ^ T = 1 := by
      rw [← mul_pow, hb]; norm_num
    have hbT0 : 0 < b ^ T := by positivity
    have hkey : b ^ T * ε ≤ 3.25 := by
      have h1 : ε ≤ 3.25 * 0.9 ^ T := by linarith
      calc b ^ T * ε ≤ b ^ T * (3.25 * 0.9 ^ T) := mul_le_mul_of_nonneg_left h1 hbT0.le
        _ = 3.25 * (b ^ T * 0.9 ^ T) := by ring
        _ = 3.25 := by rw [hbT]; ring
    have h3 : b ^ T ≤ 3.25 / ε := by rw [le_div_iff₀ hε]; exact hkey
    have hK : 0 ≤ L * b ^ 2 / (b - 1) ^ 2 := by positivity
    calc L * b ^ (T + 2) / (b - 1) ^ 2 = (L * b ^ 2 / (b - 1) ^ 2) * b ^ T := by ring
      _ ≤ (L * b ^ 2 / (b - 1) ^ 2) * (3.25 / ε) := mul_le_mul_of_nonneg_left h3 hK
      _ = _ := by ring
