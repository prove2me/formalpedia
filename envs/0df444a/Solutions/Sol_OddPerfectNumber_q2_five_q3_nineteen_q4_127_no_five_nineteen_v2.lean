-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_nineteen_q4_127_no_five_nineteen_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T07:44:53.596932+00:00
-- url     : https://prove2.me/submissions/ce8ec4ab-fa4e-408e-8c0a-e28eb16262cb

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order

theorem solution (e : Nat) :
    ¬ 5 ∣ ∑ i ∈ Finset.range (2 * e + 1), 19 ^ i := by
  apply OddPerfectNumber.geom_sum_not_dvd_of_even_order
  have horder : orderOf (19 : ZMod 5) = 2 := by
    apply (orderOf_eq_iff (x := (19 : ZMod 5)) (by norm_num)).2
    constructor
    · decide
    · intro n hn hnpos
      interval_cases n <;> decide
  change Even (orderOf (19 : ZMod 5))
  rw [horder]
  exact ⟨1, by norm_num⟩
