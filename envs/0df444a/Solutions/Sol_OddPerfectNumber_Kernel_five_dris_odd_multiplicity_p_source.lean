-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_dris_odd_multiplicity_p_source
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T15:23:17.328648+00:00
-- url     : https://prove2.me/submissions/548337b6-9151-45ec-9e52-8e443bd2003a

import Mathlib

open ArithmeticFunction in
theorem b860b1b5_sigma_sq_prod (m : ℕ) (hm : m ≠ 0) :
    (∑ d ∈ (m ^ 2).divisors, d) =
      ∏ t ∈ m.primeFactors, ∑ i ∈ Finset.range (2 * m.factorization t + 1), t ^ i := by
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
  rw [← sigma_one_apply, IsMultiplicative.multiplicative_factorization _ isMultiplicative_sigma hm2,
    Finsupp.prod, Nat.support_factorization, Nat.primeFactors_pow _ two_ne_zero]
  refine Finset.prod_congr rfl fun t ht => ?_
  rw [Nat.factorization_pow, sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors ht)]
  simp

theorem solution (p m d1 q r : Nat) (hp : p.Prime)
    (hp2 : p != 2) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : Not (Dvd.dvd p m))
    (hq : q.Prime) (hr : r.Prime) (hqr : q < r)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r)))
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * (d1 ^ 2 * (q * r))) :
    exists t : Nat, t.Prime /\ Dvd.dvd t m /\
      Dvd.dvd p (∑ i ∈ Finset.range (2 * m.factorization t + 1), t ^ i) /\
      Not (Even ((∑ i ∈ Finset.range (2 * m.factorization t + 1), t ^ i).factorization p)) := by
  have hp2' : p ≠ 2 := by simpa using hp2
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  set s := d1 ^ 2 * (q * r) with hs
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    exact pow_ne_zero 2 hm0 (by omega)
  have hps : ¬ p ∣ s := by
    intro hd
    have h2m : p ∣ 2 * m ^ 2 := h1 ▸ dvd_mul_of_dvd_right hd _
    rcases (Nat.Prime.dvd_mul hp).1 h2m with h | h
    · exact hp2' ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
    · exact hpm (hp.dvd_of_dvd_pow h)
  have hv : (∑ d ∈ (m ^ 2).divisors, d).factorization p = 5 := by
    rw [h2, Nat.factorization_mul (pow_ne_zero 5 hp.ne_zero) hs0, Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, hp.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd hps]
    rfl
  set g : ℕ → ℕ := fun t => ∑ i ∈ Finset.range (2 * m.factorization t + 1), t ^ i with hg
  have hg0 : ∀ t ∈ m.primeFactors, g t ≠ 0 := by
    intro t ht
    have : 0 < g t := Finset.sum_pos (fun i _ => pow_pos (Nat.prime_of_mem_primeFactors ht).pos i)
      ⟨0, by simp⟩
    omega
  rw [b860b1b5_sigma_sq_prod m hm0, Nat.factorization_prod hg0, Finsupp.coe_finsetSum,
    Finset.sum_apply] at hv
  by_contra hcon
  push Not at hcon
  have heven : Even (∑ t ∈ m.primeFactors, (g t).factorization p) := by
    apply Finset.even_sum
    intro t ht
    by_contra hodd
    have hne : (g t).factorization p ≠ 0 := by
      intro h0; rw [h0] at hodd; exact hodd ⟨0, rfl⟩
    exact hodd (hcon t (Nat.prime_of_mem_primeFactors ht) (Nat.dvd_of_mem_primeFactors ht)
      (Nat.dvd_of_factorization_pos hne))
  rw [hv] at heven
  exact absurd heven (by decide)
