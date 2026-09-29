-- Prove2me | solution 1 for OddPerfectNumber.k_one_huniq_from_canonical
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T17:21:01.96831+00:00
-- url     : https://prove2.me/submissions/5e275c72-18f4-42ef-895d-d48372b15e81

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_exact_valuation_one
import Theorems.Thm_OddPerfectNumber_k_one_unique_p_source

open OddPerfectNumber

theorem solution (p m d q : Nat)
    (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hdvd : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hqmem : q ∈ (m ^ 2).primeFactors)
    (hqdvd : p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i) :
    ∀ y ∈ (m ^ 2).primeFactors,
      p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization y + 1), y ^ i → y = q := by
  have hval : padicValNat p (∑ x ∈ (m ^ 2).divisors, x) = 1 :=
    k_one_exact_valuation_one p m d hp hpm hdvd hsig
  obtain ⟨q0, ⟨hq0mem, hq0dvd⟩, huniq⟩ :=
    k_one_unique_p_source p m d hp hsig hval
  have hqeq : q = q0 := huniq q ⟨hqmem, hqdvd⟩
  intro y hym hyd
  exact (huniq y ⟨hym, hyd⟩).trans hqeq.symm
