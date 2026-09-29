-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_nineteen_q4_127_absurd_from_sources_v4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T02:12:19.370255+00:00
-- url     : https://prove2.me/submissions/ea626c80-e6a2-4d79-8654-a06e3bb5baa4

import Mathlib
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_five_dvd_sigma_v4
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_product_no_five

theorem solution (p m d sigma a b c e : Nat)
    (hp : p.Prime)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsigma : sigma = p * d)
    (hD : (p + 1) / 2 < 185)
    (hpow : 5 ^ 6 ∣ m ^ 2)
    (hlocal : sigma =
      (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (e + 1), 127 ^ i))
    (h3 : ¬ 5 ∣ ∑ i ∈ Finset.range (a + 1), 3 ^ i)
    (h19 : ¬ 5 ∣ ∑ i ∈ Finset.range (c + 1), 19 ^ i)
    (h127 : ¬ 5 ∣ ∑ i ∈ Finset.range (e + 1), 127 ^ i) :
    False := by
  have h5 : 5 ∣ sigma :=
    OddPerfectNumber.q2_five_q3_nineteen_q4_127_five_dvd_sigma_v4
      p m d sigma hp hprod hsigma hD hpow
  have hno : ¬ 5 ∣ sigma := by
    rw [hlocal]
    exact OddPerfectNumber.q2_five_q3_nineteen_q4_127_product_no_five
      a b c e h3 h19 h127
  exact hno h5
