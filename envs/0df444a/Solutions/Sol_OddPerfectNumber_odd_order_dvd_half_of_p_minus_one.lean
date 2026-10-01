-- Prove2me | solution 1 for OddPerfectNumber.odd_order_dvd_half_of_p_minus_one
-- status  : ACCEPTED   (disprove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T20:01:04.139177+00:00
-- url     : https://prove2.me/submissions/77488860-d5fe-49ab-a24a-d0c2134f7915

import Mathlib

theorem solution : ¬ (∀ {p t : Nat}, (hp : p.Prime) → (hp4 : p % 4 = 1) →
    (hpt : Not (Dvd.dvd p t)) → (hord : 1 < orderOf (t : ZMod p)) →
    Dvd.dvd (orderOf (t : ZMod p)) ((p - 1) / 2)) := by
  intro h
  have ho : orderOf (2 : ZMod 5) = 4 := by
    apply (orderOf_eq_iff (by norm_num : 0 < 4)).2
    constructor
    · decide
    · intro m hm hm0
      interval_cases m <;> decide
  have hc := h (p := 5) (t := 2) (by norm_num) (by norm_num) (by norm_num)
    (by simpa [ho])
  norm_num [ho] at hc
