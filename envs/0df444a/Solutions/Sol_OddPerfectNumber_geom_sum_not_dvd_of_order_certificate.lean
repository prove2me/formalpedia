-- Prove2me | solution 1 for OddPerfectNumber.geom_sum_not_dvd_of_order_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T12:30:14.631038+00:00
-- url     : https://prove2.me/submissions/7a02789f-e02b-41f4-9752-c4be93a99d4a

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_dvd_implies_order_dvd

theorem solution {p q e : Nat}
    (hord : ¬ orderOf (q : ZMod p) ∣ 2 * e + 1) :
    ¬ p ∣ ∑ i ∈ Finset.range (2 * e + 1), q ^ i := by
  intro hdiv
  exact hord (OddPerfectNumber.geom_sum_dvd_implies_order_dvd hdiv)
