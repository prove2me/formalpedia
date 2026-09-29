-- Prove2me | solution 1 for OddPerfectNumber.geom_ratio_lower_three_ge_two_sharp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T22:41:28.100666+00:00
-- url     : https://prove2.me/submissions/3e01b3a8-02b4-4b54-b8d0-23df69eb4a38

import Mathlib

theorem solution (n : Nat) (hn : 2 ≤ n) :
    13 * 3 ^ n ≤ 9 * (∑ i ∈ Finset.range (n + 1), 3 ^ i) := by
  revert hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      by_cases hbase : n < 3
      · interval_cases n <;> norm_num at hn <;> norm_num
      · have hnpos : 0 < n := by omega
        have hprev := ih (n - 1) (by omega) (by omega)
        have hidx : n - 1 + 1 = n := by omega
        have hprev' :
            13 * 3 ^ (n - 1) ≤
              9 * (∑ i ∈ Finset.range n, 3 ^ i) := by
          rw [← hidx]
          exact hprev
        have hsum :
            (∑ i ∈ Finset.range (n + 1), 3 ^ i) =
              (∑ i ∈ Finset.range n, 3 ^ i) + 3 ^ n := by
          rw [Finset.sum_range_succ]
        have hpow : 3 ^ n = 3 ^ (n - 1) * 3 := by
          rw [← pow_succ]
          congr 1
          omega
        rw [hsum, hpow]
        omega
