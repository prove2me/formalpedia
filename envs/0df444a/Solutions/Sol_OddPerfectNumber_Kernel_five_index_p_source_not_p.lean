-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_index_p_source_not_p
-- status  : ACCEPTED   (prove)
-- author  : @os0xcom
-- created : 2026-10-03T16:12:01.282079+00:00
-- url     : https://prove2.me/submissions/4905d79a-ff7c-4ebb-bb4a-7011517558f2

import Mathlib

theorem solution (p k m : Nat) (hp : p.Prime) (hk : 1 ≤ k)
    (hm2 : m ^ 2 != 0) (hpm : Not (Dvd.dvd p m))
    (hdvd : Dvd.dvd (p ^ k) (∑ x ∈ (m ^ 2).divisors, x)) :
    exists q : Nat, Dvd.dvd q (m ^ 2) /\ Not (Dvd.dvd p q) /\
      Dvd.dvd p (∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i) := by
  have hn : m ^ 2 ≠ 0 := by
    intro h
    simp [h] at hm2
  have hpdvd : p ∣ ∑ x ∈ (m ^ 2).divisors, x :=
    dvd_trans (dvd_pow_self p (by omega)) hdvd
  rw [Nat.sum_divisors hn] at hpdvd
  obtain ⟨q, hq, hpq⟩ :=
    (hp.prime.dvd_finsetProd_iff
      (fun q => ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i)).mp hpdvd
  refine ⟨q, Nat.dvd_of_mem_primeFactors hq, ?_, hpq⟩
  intro hdiv
  have hqe : p = q :=
    (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hq)).mp hdiv
  apply hpm
  have hpow : p ∣ m ^ 2 := by simpa [hqe] using Nat.dvd_of_mem_primeFactors hq
  exact hp.dvd_of_dvd_pow hpow
