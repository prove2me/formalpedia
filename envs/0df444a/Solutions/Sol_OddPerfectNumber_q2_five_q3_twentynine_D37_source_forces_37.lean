-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentynine_D37_source_forces_37
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T07:01:39.082543+00:00
-- url     : https://prove2.me/submissions/ae044c11-802e-4af2-b12d-e1e99089495f

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order
import Theorems.Thm_OddPerfectNumber_even_orders_mod_73_q3_twentynine

theorem solution (sigma a b c e : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), 37 ^ i))
    (hdiv : 73 ∣ sigma)
    (haEven : Even a) (hbEven : Even b) (hcEven : Even c) (heEven : Even e) :
    73 ∣ ∑ i ∈ Finset.range (2 * e + 1), 37 ^ i := by
  have hbase := OddPerfectNumber.even_orders_mod_73_q3_twentynine
  have hno3 : ¬ 73 ∣ ∑ i ∈ Finset.range (2 * a + 1), 3 ^ i := by
    exact OddPerfectNumber.geom_sum_not_dvd_of_even_order (e := a) hbase.1
  have hno5 : ¬ 73 ∣ ∑ i ∈ Finset.range (2 * b + 1), 5 ^ i := by
    exact OddPerfectNumber.geom_sum_not_dvd_of_even_order (e := b) hbase.2.1
  have hno29 : ¬ 73 ∣ ∑ i ∈ Finset.range (2 * c + 1), 29 ^ i := by
    exact OddPerfectNumber.geom_sum_not_dvd_of_even_order (e := c) hbase.2.2
  have hprod : 73 ∣
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), 37 ^ i) := by
    simpa [hsigma] using hdiv
  have hp : Nat.Prime 73 := by norm_num
  rcases hp.dvd_mul.mp hprod with hrest | h37
  · rcases hp.dvd_mul.mp hrest with hrest' | h29
    · rcases hp.dvd_mul.mp hrest' with h3 | h5
      · exact False.elim (hno3 h3)
      · exact False.elim (hno5 h5)
    · exact False.elim (hno29 h29)
  · exact h37
