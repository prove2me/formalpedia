-- Prove2me | solution 1 for OddPerfectNumber.geom_sum_last_three_terms_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T18:20:00.255489+00:00
-- url     : https://prove2.me/submissions/9f59db61-4f1b-4f48-8b53-690a149cbca3

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_last_two_terms_le

theorem solution (q e : Nat) (he : 2 ≤ e) :
    q ^ e + q ^ (e - 1) + q ^ (e - 2) ≤
      ∑ i ∈ Finset.range (e + 1), q ^ i := by
  have hlast := OddPerfectNumber.geom_sum_last_two_terms_le q (e - 1) (by omega)
  have hstep := Nat.add_le_add_left hlast (q ^ e)
  have heq0 : e - 1 + 1 = e := by omega
  have hrange : Finset.range (e - 1 + 1) = Finset.range e := by rw [heq0]
  rw [hrange] at hstep
  have hdecomp :
      (∑ i ∈ Finset.range (e + 1), q ^ i) =
        (∑ i ∈ Finset.range e, q ^ i) + q ^ e := by
    rw [show e + 1 = e + 1 by rfl, Finset.sum_range_succ]
  rw [hdecomp]
  have heq : (e - 1) - 1 = e - 2 := by omega
  simpa [heq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstep
