-- Prove2me | solution 1 for OddPerfectNumber.geom_sum_first_three_terms_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T14:33:09.01398+00:00
-- url     : https://prove2.me/submissions/e9fea440-b5c0-46b1-983c-2e252ae409d1

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_last_term_le

theorem solution (q n : Nat) (hn : 2 ≤ n) :
    q ^ n + q ^ (n - 1) + q ^ (n - 2) ≤
      ∑ i ∈ Finset.range (n + 1), q ^ i := by
  have hsub : Finset.range ((n - 2) + 1) ⊆ Finset.range (n + 1) := by
    intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  have hprev :
      (∑ i ∈ Finset.range ((n - 2) + 1), q ^ i) ≤
        ∑ i ∈ Finset.range (n + 1), q ^ i := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro i hi hnot
      positivity)
  have hdecomp :
      (∑ i ∈ Finset.range (n + 1), q ^ i) =
        (∑ i ∈ Finset.range ((n - 2) + 1), q ^ i) +
          q ^ (n - 1) + q ^ n := by
    rw [show n + 1 = ((n - 2) + 1) + 2 by omega]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    congr 1
    · rw [show n - 2 + 1 = n - 1 by omega]
    · rw [show n - 2 + 2 = n by omega]
  have hlast : q ^ (n - 2) ≤
      ∑ i ∈ Finset.range ((n - 2) + 1), q ^ i := by
    exact OddPerfectNumber.geom_sum_last_term_le q (n - 2)
  have hstep := Nat.add_le_add_left hlast (q ^ (n - 1) + q ^ n)
  simpa [hdecomp, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstep
