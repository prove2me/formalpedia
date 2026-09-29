-- Prove2me | solution 1 for OddPerfectNumber.geom_sum_not_dvd_of_even_order
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T00:05:22.907499+00:00
-- url     : https://prove2.me/submissions/a96f6664-1625-4dc3-9dfd-a0ee332183f9

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_dvd_implies_order_dvd

theorem solution {p q e : Nat}
    (heven : Even (orderOf (q : ZMod p))) :
    ¬ p ∣ ∑ i ∈ Finset.range (2 * e + 1), q ^ i := by
  intro hdiv
  have hord := OddPerfectNumber.geom_sum_dvd_implies_order_dvd hdiv
  rcases heven with ⟨k, hk⟩
  rcases hord with ⟨c, hc⟩
  have hEq : 2 * e + 1 = 2 * (k * c) := by
    calc
      2 * e + 1 = (orderOf (q : ZMod p)) * c := hc
      _ = (k + k) * c := by rw [hk]
      _ = 2 * (k * c) := by ring
  have htwo : 2 ∣ 2 * e + 1 := by
    exact ⟨k * c, hEq⟩
  omega
