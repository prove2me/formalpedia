-- Prove2me | solution 1 for OddPerfectNumber.sigma_five_small_even_values
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T18:38:59.977301+00:00
-- url     : https://prove2.me/submissions/502a945e-2779-4ac9-ba5c-7763edd75058

import Mathlib

theorem solution :
    ((∑ i ∈ Finset.range (2 + 1), 5 ^ i) = 31) ∧
    ((∑ i ∈ Finset.range (4 + 1), 5 ^ i) = 781) ∧
    ((∑ i ∈ Finset.range (6 + 1), 5 ^ i) = 19531) := by
  norm_num [Finset.sum_range_succ]
