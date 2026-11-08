-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P30.powerInequality
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-07T16:35:46.375307+00:00
-- url     : https://prove2.me/submissions/273becb9-e16a-4eb0-aceb-eafe72bbd4e6

import Mathlib

/-- Lemma 7.4: `4 p^k - 3 ≤ (4p - 3)^k` for `k ≥ 1`, `p ∈ [0,1]`, whenever the left side is nonnegative. -/
theorem solution (k p : ℝ) (hk : 1 ≤ k) (hp : p ∈ Set.Icc 0 1)
    (hrhs : 0 ≤ 4 * Real.rpow p k - 3) :
    4 * Real.rpow p k - 3 ≤ Real.rpow (4 * p - 3) k := by
  have hp0 : 0 ≤ p := hp.1
  have hp1 : p ≤ 1 := hp.2
  have hpk_le : p ^ k ≤ p := Real.rpow_le_self_of_le_one hp0 hp1 hk
  have hrhs' : (0 : ℝ) ≤ 4 * p ^ k - 3 := hrhs
  have hq0 : 0 ≤ 4 * p - 3 := by nlinarith [hrhs', hpk_le]
  have hconv := convexOn_rpow (p := k) hk
  have hconv' : ((1 / 4 : ℝ) * (4 * p - 3) + (3 / 4 : ℝ) * 1) ^ k ≤
      (1 / 4 : ℝ) * ((4 * p - 3) ^ k) + (3 / 4 : ℝ) * ((1 : ℝ) ^ k) := by
    have h := hconv.2 (by exact hq0) (by norm_num : (1:ℝ) ∈ Set.Ici 0)
      (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num : (0:ℝ) ≤ 3/4)
      (by norm_num : (1:ℝ)/4 + 3/4 = 1)
    simpa [smul_eq_mul] using h
  have hsimp : (1 / 4 : ℝ) * (4 * p - 3) + (3 / 4 : ℝ) * 1 = p := by ring
  rw [hsimp] at hconv'
  have hone : (1 : ℝ) ^ k = 1 := Real.one_rpow k
  rw [hone] at hconv'
  change 4 * p ^ k - 3 ≤ (4 * p - 3) ^ k
  nlinarith [hconv']
