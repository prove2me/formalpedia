-- Prove2me | solution 1 for QApproxCount.Counting.eqs_30_32
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:14:29.712916+00:00
-- url     : https://prove2.me/submissions/75dbb2c1-3c74-43b6-a4eb-b243c66a544c

import Mathlib
import Definitions.Def_QApproxCount_Counting_Algorithm
set_option autoImplicit false

open QApproxCount.Counting

theorem solution (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (T : ℕ)
    (hT : ε / 5 ≤ 0.65 * (0.9 : ℝ) ^ T) :
    ∑ t ∈ Finset.range (T + 1), deltaT ε δ t ≤ δ / 2 := by
  set b : ℝ := 10 / 9 with hb
  have hterm : ∀ t : ℕ, deltaT ε δ t = δ * ε / 65 * b ^ t := by
    intro t
    unfold deltaT
    rw [zpow_neg, zpow_natCast, hb, ← inv_pow]
    norm_num
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hgeom : (∑ t ∈ Finset.range (T + 1), b ^ t) * (b - 1) = b ^ (T + 1) - 1 :=
    geom_sum_mul b (T + 1)
  have hb1 : b - 1 = 1 / 9 := by rw [hb]; norm_num
  have hS : ∑ t ∈ Finset.range (T + 1), b ^ t ≤ 10 * b ^ T := by
    rw [hb1] at hgeom
    have : ∑ t ∈ Finset.range (T + 1), b ^ t = 9 * (b ^ (T + 1) - 1) := by linarith
    rw [this, pow_succ]
    have : (0:ℝ) < b ^ T := by rw [hb]; positivity
    rw [hb]; nlinarith
  have h09 : (0 : ℝ) < 0.9 ^ T := by positivity
  have hbT : b ^ T * (0.9 : ℝ) ^ T = 1 := by
    rw [← mul_pow, hb]; norm_num
  have hbT0 : 0 < b ^ T := by rw [hb]; positivity
  have hkey : b ^ T * ε ≤ 3.25 := by
    have h1 : ε ≤ 3.25 * 0.9 ^ T := by linarith
    calc b ^ T * ε ≤ b ^ T * (3.25 * 0.9 ^ T) := mul_le_mul_of_nonneg_left h1 hbT0.le
      _ = 3.25 * (b ^ T * 0.9 ^ T) := by ring
      _ = 3.25 := by rw [hbT]; ring
  have hc : 0 ≤ δ * ε / 65 := by positivity
  calc δ * ε / 65 * ∑ t ∈ Finset.range (T + 1), b ^ t
      ≤ δ * ε / 65 * (10 * b ^ T) := mul_le_mul_of_nonneg_left hS hc
    _ = δ * 10 / 65 * (b ^ T * ε) := by ring
    _ ≤ δ * 10 / 65 * 3.25 := mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = δ / 2 := by ring
