-- Prove2me | solution 1 for OddPerfectNumber.geom_sum_dvd_implies_order_dvd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T12:26:49.116368+00:00
-- url     : https://prove2.me/submissions/5be99cf3-8be7-4577-9b6d-fa9bcdcd5426

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_dvd_implies_zmod_pow_eq_one

theorem solution {p q e : Nat}
    (h : p ∣ ∑ i ∈ Finset.range (2 * e + 1), q ^ i) :
    orderOf (q : ZMod p) ∣ 2 * e + 1 := by
  exact orderOf_dvd_of_pow_eq_one
    (OddPerfectNumber.geom_sum_dvd_implies_zmod_pow_eq_one h)
