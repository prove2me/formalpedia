-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_nineteen_q4_31_minimum_abundance_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T23:35:48.623685+00:00
-- url     : https://prove2.me/submissions/10ba71f8-2f13-4079-9031-ae376f51a84c

import Mathlib

theorem solution :
    2 * (3 ^ 6 * 5 ^ 2 * 19 ^ 2 * 31 ^ 2) <
      (∑ i ∈ Finset.range (6 + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2 + 1), 31 ^ i) := by
  norm_num [Finset.sum_range_succ]
