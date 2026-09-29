-- Prove2me | solution 1 for OddPerfectNumber.geom_ratio_lower_eleven_ge_two_sharp_v3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T22:31:06.931573+00:00
-- url     : https://prove2.me/submissions/60d8f452-526f-4f60-8c8c-829aecf89d7d

import Mathlib

theorem solution (n : Nat) (hn : 2 ≤ n) :
    133 * 11 ^ n ≤ 121 * (∑ i ∈ Finset.range (n + 1), 11 ^ i) := by
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
            133 * 11 ^ (n - 1) ≤
              121 * (∑ i ∈ Finset.range n, 11 ^ i) := by
          rw [← hidx]
          exact hprev
        have hsum :
            (∑ i ∈ Finset.range (n + 1), 11 ^ i) =
              (∑ i ∈ Finset.range n, 11 ^ i) + 11 ^ n := by
          rw [Finset.sum_range_succ]
        have hpow : 11 ^ n = 11 ^ (n - 1) * 11 := by
          rw [← pow_succ]
          congr 1
          omega
        rw [hsum, hpow]
        omega
