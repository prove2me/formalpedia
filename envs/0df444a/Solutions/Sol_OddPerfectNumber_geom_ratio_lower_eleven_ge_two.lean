-- Prove2me | solution 1 for OddPerfectNumber.geom_ratio_lower_eleven_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T22:15:08.18267+00:00
-- url     : https://prove2.me/submissions/88898515-7ca3-4e5e-816f-96426d3eb45e

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_last_term_le

theorem solution (n : Nat) :
    10 * 11 ^ n ≤ 11 * (∑ i ∈ Finset.range (n + 1), 11 ^ i) := by
  have hlast := OddPerfectNumber.geom_sum_last_term_le 11 n
  omega
