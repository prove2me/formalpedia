-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_r_has_non_self_sigma_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T21:24:30.781145+00:00
-- url     : https://prove2.me/submissions/87ea5bbd-2bda-4f08-9d0e-be878c1c560e

-- Repair of 7386-class CE (E01/E02 L20/L22, full report read).
-- Root cause: published helpers bind (p m d1 q r : Nat) EXPLICITLY, so bare
-- `hp` filled p. Fix: pass all five Nats explicitly.import Mathlib
import Theorems.Thm_OddPerfectNumber_Kernel_square_witness_of_first_dris
import Theorems.Thm_OddPerfectNumber_Kernel_five_two_prime_cyclotomic_primes_dvd_m
import Theorems.Thm_OddPerfectNumber_Kernel_five_two_prime_index_primes_dvd_sigma
import Theorems.Thm_OddPerfectNumber_Kernel_index_prime_has_non_self_sigma_source

theorem solution (p m d1 q r : Nat)
    (hp : p.Prime) (hp2 : p != 2) (hp4 : p % 4 = 1)
    (hm : Odd m) (hpm : ¬ p ∣ m)
    (hq : q.Prime) (hr : r.Prime) (hqr : q < r)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) *
      (d1 ^ 2 * (q * r)))
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * (d1 ^ 2 * (q * r))) :
    exists t : Nat, t.Prime /\ Dvd.dvd t m /\ Not (Dvd.dvd t r) /\
      Dvd.dvd r (∑ i ∈ Finset.range ((m ^ 2).factorization t + 1), t ^ i) := by
  have hsq := OddPerfectNumber.Kernel.square_witness_of_first_dris
    p m d1 q r hp hp2 hm hq hr h1
  have hdiv := OddPerfectNumber.Kernel.five_two_prime_cyclotomic_primes_dvd_m
    p m d1 q r hp hp2 hp4 hm hpm hq hr hqr h1 hsq
  have hsig := (OddPerfectNumber.Kernel.five_two_prime_index_primes_dvd_sigma
    p m d1 q r h2).2
  obtain ⟨k, hk⟩ := hm
  have hm0 : m ≠ 0 := by omega
  have hm2 : m ^ 2 != 0 := by simpa using (pow_ne_zero 2 hm0)
  exact OddPerfectNumber.Kernel.index_prime_has_non_self_sigma_source
    hr hdiv.2 hm2 hsig
