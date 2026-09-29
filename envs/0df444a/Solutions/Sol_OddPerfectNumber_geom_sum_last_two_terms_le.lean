-- Prove2me | solution 1 for OddPerfectNumber.geom_sum_last_two_terms_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T01:12:58.837269+00:00
-- url     : https://prove2.me/submissions/e87cc35b-8286-4e26-8567-0497f111259c

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_last_term_le

theorem solution (q e : Nat) (he : 1 ≤ e) :
    q ^ e + q ^ (e - 1) ≤ ∑ i ∈ Finset.range (e + 1), q ^ i := by
  have hsub : Finset.range ((e - 1) + 1) ⊆ Finset.range (e + 1) := by
    intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  have hprev :
      (∑ i ∈ Finset.range ((e - 1) + 1), q ^ i) ≤
        ∑ i ∈ Finset.range (e + 1), q ^ i := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro i hi hnot
      positivity)
  have hdecomp :
      (∑ i ∈ Finset.range (e + 1), q ^ i) =
        (∑ i ∈ Finset.range ((e - 1) + 1), q ^ i) + q ^ e := by
    rw [show e + 1 = ((e - 1) + 1) + 1 by omega]
    rw [Finset.sum_range_succ]
    congr 1
    rw [show e - 1 + 1 = e by omega]
  have hlast := OddPerfectNumber.geom_sum_last_term_le q (e - 1)
  have hstep := Nat.add_le_add_left hlast (q ^ e)
  simpa [hdecomp, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstep
