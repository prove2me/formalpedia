-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_nineteen_q4_127_no_five_127
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T08:00:50.723953+00:00
-- url     : https://prove2.me/submissions/b61284d3-6ff9-4ec1-bdb7-a46ba6f72912

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order

theorem solution (e : Nat) :
    ¬ 5 ∣ ∑ i ∈ Finset.range (2 * e + 1), 127 ^ i := by
  apply OddPerfectNumber.geom_sum_not_dvd_of_even_order
  have horder : orderOf (127 : ZMod 5) = 4 := by
    apply (orderOf_eq_iff (x := (127 : ZMod 5)) (by norm_num)).2
    constructor
    · decide
    · intro n hn hnpos
      interval_cases n <;> decide
  change Even (orderOf (127 : ZMod 5))
  rw [horder]
  exact ⟨2, by norm_num⟩
