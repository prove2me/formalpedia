-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_exp_six_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T19:20:55.378463+00:00
-- url     : https://prove2.me/submissions/a10ee3d0-2905-4db2-ad4e-3d7acd5d86cd

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_external_nineteen_five_three_one_absurd

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19531 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 6) :
    False := by
  have hm0 : m ≠ 0 := by
    rcases hm with ⟨k, hk⟩
    omega
  have hn0 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hlocal := OddPerfectNumber.local_sigma_factor_dvd_global
    (m ^ 2) 5 hn0 h5mem
  rw [h5exp] at hlocal
  have hlocal6 : (∑ i ∈ Finset.range (6 + 1), 5 ^ i) ∣
      ∑ x ∈ (m ^ 2).divisors, x := hlocal
  have h19531local : 19531 ∣ ∑ i ∈ Finset.range (6 + 1), 5 ^ i := by
    norm_num [Finset.sum_range_succ]
  have h19531global : 19531 ∣ ∑ x ∈ (m ^ 2).divisors, x :=
    dvd_trans h19531local hlocal6
  have hddvd : d ∣ m ^ 2 := by
    refine ⟨(p + 1) / 2, ?_⟩
    simpa [Nat.mul_comm] using hprod
  exact OddPerfectNumber.four_support_external_nineteen_five_three_one_absurd
    p m d q4 hp hp4 hm0 hsig hddvd hsupport hq4prime hq4gt h19531global
