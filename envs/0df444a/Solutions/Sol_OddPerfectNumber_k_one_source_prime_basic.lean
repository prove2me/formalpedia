-- Prove2me | solution 1 for OddPerfectNumber.k_one_source_prime_basic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T09:14:46.944817+00:00
-- url     : https://prove2.me/submissions/54412c5f-e089-4ddd-b429-3e492c884cc6

import Mathlib

-- STAGED, NOT YET SUBMITTED (awaits publish job beb0d170 for the child).
-- Elementary prime-support packaging; every lemma name verified against
-- the pinned Mathlib sources (primeFactors API, Parity.lean).
theorem solution (p m q : Nat)
    (hpm : ¬ p ∣ m) (hm_odd : Odd m)
    (hqmem : q ∈ (m ^ 2).primeFactors) :
    q.Prime ∧ q ∣ m ∧ q ≠ p ∧ Odd q := by
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hqmem
  have hqdvd : q ∣ m ^ 2 := Nat.dvd_of_mem_primeFactors hqmem
  have hqm : q ∣ m := by
    have h : q ∣ m * m := by simpa [pow_two] using hqdvd
    rcases (hqprime.dvd_mul).mp h with h | h <;> exact h
  refine ⟨hqprime, hqm, ?_, ?_⟩
  · intro heq
    apply hpm
    rw [← heq]
    exact hqm
  · by_contra h
    rw [Nat.not_odd_iff_even] at h
    have hm_even : Even m := h.trans_dvd hqm
    exact (Nat.not_even_iff_odd.mpr hm_odd) hm_even
