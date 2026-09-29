-- Prove2me | solution 1 for OddPerfectNumber.k_one_p1709_no_local_sigma_source_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T04:21:35.387539+00:00
-- url     : https://prove2.me/submissions/88be3e23-410f-4112-afc8-1be0aca50a36

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order

theorem solution (sigma a b c e : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (e + 1), 101 ^ i))
    (hdiv : 1709 ∣ sigma)
    (h3 : Even (orderOf (3 : ZMod 1709)))
    (h5 : Even (orderOf (5 : ZMod 1709)))
    (h19 : Even (orderOf (19 : ZMod 1709)))
    (h101 : Even (orderOf (101 : ZMod 1709)))
    (haEven : Even a) (hbEven : Even b) (hcEven : Even c) (heEven : Even e) :
    False := by
  rcases haEven with ⟨a0, ha0⟩
  rcases hbEven with ⟨b0, hb0⟩
  rcases hcEven with ⟨c0, hc0⟩
  rcases heEven with ⟨e0, he0⟩
  have ha2 : a = 2 * a0 := by omega
  have hb2 : b = 2 * b0 := by omega
  have hc2 : c = 2 * c0 := by omega
  have he2 : e = 2 * e0 := by omega
  have hno3 : ¬ 1709 ∣ ∑ i ∈ Finset.range (a + 1), 3 ^ i := by
    simpa [ha2] using (OddPerfectNumber.geom_sum_not_dvd_of_even_order (e := a0) h3)
  have hno5 : ¬ 1709 ∣ ∑ i ∈ Finset.range (b + 1), 5 ^ i := by
    simpa [hb2] using (OddPerfectNumber.geom_sum_not_dvd_of_even_order (e := b0) h5)
  have hno19 : ¬ 1709 ∣ ∑ i ∈ Finset.range (c + 1), 19 ^ i := by
    simpa [hc2] using (OddPerfectNumber.geom_sum_not_dvd_of_even_order (e := c0) h19)
  have hno101 : ¬ 1709 ∣ ∑ i ∈ Finset.range (e + 1), 101 ^ i := by
    simpa [he2] using (OddPerfectNumber.geom_sum_not_dvd_of_even_order (e := e0) h101)
  have hp : Nat.Prime 1709 := by norm_num
  have h := hdiv
  rw [hsigma] at h
  rcases hp.dvd_mul.mp h with hleft | h101div
  · rcases hp.dvd_mul.mp hleft with hleft' | h19div
    · rcases hp.dvd_mul.mp hleft' with h3div | h5div
      · exact hno3 h3div
      · exact hno5 h5div
    · exact hno19 h19div
  · exact hno101 h101div
