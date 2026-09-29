-- Prove2me | solution 1 for OddPerfectNumber.four_support_scaled_abundance_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T15:52:59.091981+00:00
-- url     : https://prove2.me/submissions/7ebc2ac8-965d-4a36-9582-389dd351ced0

import Mathlib

theorem solution (x y : Nat)
    (hupper : 2880 * x < 5005 * y)
    (hlower : 5184 * y ≤ 2880 * x) :
    False := by
  have hcoef : 5005 * y < 5184 * y := by
    have hy : 0 < y := by omega
    exact (Nat.mul_lt_mul_right hy).2 (by norm_num)
  have hcontra : 2880 * x < 5184 * y :=
    lt_of_lt_of_le hupper (Nat.le_of_lt hcoef)
  exact (Nat.not_lt_of_ge hlower) hcontra
