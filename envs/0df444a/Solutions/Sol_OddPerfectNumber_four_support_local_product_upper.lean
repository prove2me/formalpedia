-- Prove2me | solution 1 for OddPerfectNumber.four_support_local_product_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T15:49:45.881058+00:00
-- url     : https://prove2.me/submissions/f63469f6-c8fd-4382-999c-e6919119deae

import Mathlib

theorem solution (x1 x2 x3 x4 y1 y2 y3 y4 : Nat)
    (h1 : 4 * x1 < 5 * y1)
    (h2 : 6 * x2 < 7 * y2)
    (h3 : 10 * x3 < 11 * y3)
    (h4 : 12 * x4 < 13 * y4) :
    2880 * (x1 * x2 * x3 * x4) < 5005 * (y1 * y2 * y3 * y4) := by
  have h12 := Nat.mul_lt_mul_of_lt_of_lt h1 h2
  have h123 := Nat.mul_lt_mul_of_lt_of_lt h12 h3
  have h1234 := Nat.mul_lt_mul_of_lt_of_lt h123 h4
  calc
    2880 * (x1 * x2 * x3 * x4) =
        (4 * x1) * (6 * x2) * (10 * x3) * (12 * x4) := by ring
    _ < (5 * y1) * (7 * y2) * (11 * y3) * (13 * y4) := h1234
    _ = 5005 * (y1 * y2 * y3 * y4) := by ring
