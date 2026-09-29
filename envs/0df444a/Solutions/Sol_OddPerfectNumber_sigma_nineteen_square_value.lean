-- Prove2me | solution 1 for OddPerfectNumber.sigma_nineteen_square_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T19:07:15.177741+00:00
-- url     : https://prove2.me/submissions/5f63ad55-3ebf-44e4-aef4-bb41c1543fae

import Mathlib

theorem solution :
    (∑ i ∈ Finset.range (2 + 1), 19 ^ i) = 3 * 127 := by
  norm_num [Finset.sum_range_succ]
