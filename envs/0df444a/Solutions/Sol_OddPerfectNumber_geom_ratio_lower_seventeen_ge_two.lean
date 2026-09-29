-- Prove2me | solution 1 for OddPerfectNumber.geom_ratio_lower_seventeen_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T12:02:28.223406+00:00
-- url     : https://prove2.me/submissions/1be15a2b-d631-4851-b824-ef47ec7a4f2d

import Mathlib

theorem solution (c : Nat) (hc : 2 ≤ c) :
    307 * 17 ^ c ≤
      289 * (∑ i ∈ Finset.range (c + 1), 17 ^ i) := by
  induction c, hc using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have hS : (∑ i ∈ Finset.range (n + 1 + 1), 17 ^ i)
        = (∑ i ∈ Finset.range (n + 1), 17 ^ i) + 17 ^ (n + 1) := by
      rw [Finset.sum_range_succ]
    have h1 : 18 * 17 ^ (n + 1) ≤ 307 * 17 ^ n := by
      have hpow : 17 ^ (n + 1) = 17 ^ n * 17 := pow_succ 17 n
      rw [hpow]
      have hle : 18 * 17 ≤ 307 := by norm_num
      calc 18 * (17 ^ n * 17) = (18 * 17) * 17 ^ n := by ring
        _ ≤ 307 * 17 ^ n := Nat.mul_le_mul_right _ hle
    have hsplit : 307 * 17 ^ (n + 1) = 18 * 17 ^ (n + 1) + 289 * 17 ^ (n + 1) := by ring
    rw [hS]
    omega
