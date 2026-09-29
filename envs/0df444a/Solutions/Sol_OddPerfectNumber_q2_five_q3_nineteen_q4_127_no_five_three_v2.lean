-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_nineteen_q4_127_no_five_three_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T07:47:04.529283+00:00
-- url     : https://prove2.me/submissions/317af843-cc29-40c4-95a2-f5541422f0a5

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order

theorem solution (e : Nat) :
    ¬ 5 ∣ ∑ i ∈ Finset.range (2 * e + 1), 3 ^ i := by
  apply OddPerfectNumber.geom_sum_not_dvd_of_even_order
  have horder : orderOf (3 : ZMod 5) = 4 := by
    apply (orderOf_eq_iff (x := (3 : ZMod 5)) (by norm_num)).2
    constructor
    · decide
    · intro n hn hnpos
      interval_cases n <;> decide
  change Even (orderOf (3 : ZMod 5))
  rw [horder]
  exact ⟨2, by norm_num⟩
