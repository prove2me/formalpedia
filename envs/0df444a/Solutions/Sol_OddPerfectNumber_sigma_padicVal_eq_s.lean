-- Prove2me | solution 1 for OddPerfectNumber.sigma_padicVal_eq_s
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T09:52:13.513743+00:00
-- url     : https://prove2.me/submissions/63e5a5f4-82eb-4e67-86b0-ca98858f5f7f

import Mathlib

-- STAGED direct proof. Lemma names verified against pinned Mathlib:
-- padicValNat.mul (needs Fact, supplied), padicValNat.eq_zero_of_not_dvd,
-- Prime.dvd_of_dvd_pow via Nat.Prime.prime.
theorem solution (r p k m s : Nat) (hr : r.Prime) (hpm : ¬ r ∣ p)
    (hs2 : 2 ≤ s)
    (hsigm : (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * s) :
    padicValNat r (∑ x ∈ (m ^ 2).divisors, x) = padicValNat r s := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hs0 : s ≠ 0 := by omega
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact hpm (dvd_zero r)
  have hpk0 : p ^ k ≠ 0 := pow_ne_zero k hp0
  have hnp : ¬ r ∣ p ^ k := fun hdvd => hpm (hr.prime.dvd_of_dvd_pow hdvd)
  rw [hsigm, padicValNat.mul hpk0 hs0,
    padicValNat.eq_zero_of_not_dvd hnp, zero_add]
