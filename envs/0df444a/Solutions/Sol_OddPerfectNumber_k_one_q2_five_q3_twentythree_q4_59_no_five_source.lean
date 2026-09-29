-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_59_no_five_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T19:38:54.005114+00:00
-- url     : https://prove2.me/submissions/b0b100a8-1900-43f1-a4fd-c15a570e589d

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order

theorem solution (e : Nat) (heven : Even e) :
    ¬ 5 ∣ ∑ i ∈ Finset.range (e + 1), 59 ^ i := by
  rcases heven with ⟨t, rfl⟩
  have horder : orderOf (59 : ZMod 5) = 2 := by
    apply (orderOf_eq_iff (x := (59 : ZMod 5)) (by norm_num)).2
    constructor
    · decide
    · intro n hn hnpos
      interval_cases n <;> decide
  have hEvenOrder : Even (orderOf (59 : ZMod 5)) := by
    simpa [horder] using (show Even 2 by norm_num)
  simpa [two_mul] using
    (OddPerfectNumber.geom_sum_not_dvd_of_even_order (p := 5) (q := 59) (e := t)
      hEvenOrder)
