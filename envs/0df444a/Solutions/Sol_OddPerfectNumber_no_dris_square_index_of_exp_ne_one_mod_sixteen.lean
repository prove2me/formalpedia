-- Prove2me | solution 1 for OddPerfectNumber.no_dris_square_index_of_exp_ne_one_mod_sixteen
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-11T19:22:30.224272+00:00
-- url     : https://prove2.me/submissions/35b3d44e-98ad-4b25-9a89-61f5ad66cb03

import Theorems.Thm_OddPerfectNumber_prime_and_exp_mod_sixteen_of_sigma_eq_two_mul_sq

open Finset

namespace DrisSquareAux

/-- `σ(p^k)` as a geometric sum. -/
lemma sigma_prime_pow (p k : ℕ) (hp : p.Prime) :
    ∑ d ∈ (p ^ k).divisors, d = ∑ i ∈ range (k + 1), p ^ i := by
  rw [Nat.sum_divisors_prime_pow hp]

/-- Geometric sums mod `r`, when `p ≡ 1 [MOD r]`. -/
lemma geom_mod (p n r : ℕ) (h : p % r = 1 % r) :
    (∑ i ∈ range n, p ^ i) % r = n % r := by
  rw [Finset.sum_nat_mod]
  have : ∀ i ∈ range n, p ^ i % r = 1 % r := by
    intro i _
    rw [Nat.pow_mod, h, ← Nat.pow_mod, one_pow]
  rw [Finset.sum_congr rfl this]
  simp [Finset.sum_const]

/-- The divisor sum of a square, factored into its local divisor sums. -/
lemma sigma_sq_local_prod {m : ℕ} (hm : m ≠ 0) :
    (∑ x ∈ (m ^ 2).divisors, x) =
      ∏ q ∈ (m ^ 2).primeFactors, ∑ i ∈ range ((m ^ 2).factorization q + 1), q ^ i := by
  have hm2 : (m ^ 2) ≠ 0 := pow_ne_zero _ hm
  have h := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).multiplicative_factorization
    (ArithmeticFunction.sigma 1) hm2
  rw [ArithmeticFunction.sigma_one_apply] at h
  rw [h, Finsupp.prod]
  rw [Nat.support_factorization]
  refine Finset.prod_congr rfl ?_
  intro q hq
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  rw [ArithmeticFunction.sigma_one_apply, sigma_prime_pow q _ hqp]

/-- A prime factor of `m²` is odd when `m` is odd. -/
lemma prime_factor_odd {m q : ℕ} (hm : Odd m) (hq : q ∈ (m ^ 2).primeFactors) : q % 2 = 1 := by
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqm : q ∣ m ^ 2 := Nat.dvd_of_mem_primeFactors hq
  rcases hqp.eq_two_or_odd with h | h
  · subst h
    have : (2 : ℕ) ∣ m := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hqm
    rw [Nat.odd_iff] at hm
    omega
  · exact h

/-- Each local divisor sum of `m²` is odd, when `m` is odd. -/
lemma local_odd {m q : ℕ} (hm : Odd m) (hq : q ∈ (m ^ 2).primeFactors) :
    (∑ i ∈ range ((m ^ 2).factorization q + 1), q ^ i) % 2 = 1 := by
  have hqodd : q % 2 = 1 := prime_factor_odd hm hq
  have hE : (m ^ 2).factorization q = 2 * m.factorization q := by
    rw [Nat.factorization_pow]
    simp
  rw [geom_mod q ((m ^ 2).factorization q + 1) 2 (by omega), hE]
  omega

/-- The divisor sum of an odd square is odd. -/
lemma sigma_sq_odd {m : ℕ} (hm : Odd m) (hm0 : m ≠ 0) :
    (∑ x ∈ (m ^ 2).divisors, x) % 2 = 1 := by
  rw [sigma_sq_local_prod hm0, Finset.prod_nat_mod]
  rw [Finset.prod_congr rfl (fun q hq => local_odd hm hq)]
  simp

/-- With a square index the first Dris relation says that `σ(p^k)` is twice a square. -/
theorem sigma_eq_two_mul_sq_of_square_index {p k m s u : ℕ} (hm : Odd m)
    (hsq : s = u ^ 2)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s)
    (h2 : (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * s) :
    ∃ w : ℕ, (∑ d ∈ (p ^ k).divisors, d) = 2 * w ^ 2 := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hsodd : s % 2 = 1 := by
    have hsdvd : s ∣ (∑ x ∈ (m ^ 2).divisors, x) := ⟨p ^ k, by rw [h2]; ring⟩
    have hodd := sigma_sq_odd hm hm0
    have h2s : ¬ (2 ∣ s) := by
      intro hd
      have := hd.trans hsdvd
      omega
    omega
  have hs0 : s ≠ 0 := by omega
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp [hsq] at hs0
  have hsm : s ∣ m ^ 2 := by
    have hd : s ∣ 2 * m ^ 2 := ⟨_, by rw [h1]; ring⟩
    have hcop : Nat.Coprime s 2 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)).symm
    exact hcop.dvd_of_dvd_mul_left hd
  have hum : u ∣ m := by
    have : u ^ 2 ∣ m ^ 2 := hsq ▸ hsm
    exact (Nat.pow_dvd_pow_iff (by norm_num)).mp this
  obtain ⟨w, hw⟩ := hum
  refine ⟨w, ?_⟩
  have hcalc : (∑ d ∈ (p ^ k).divisors, d) * u ^ 2 = (2 * w ^ 2) * u ^ 2 := by
    have hstep : (∑ d ∈ (p ^ k).divisors, d) * u ^ 2 = 2 * m ^ 2 := by rw [h1, hsq]
    rw [hstep, hw]
    ring
  have hu2 : u ^ 2 ≠ 0 := pow_ne_zero _ hu0
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hu2) hcalc

end DrisSquareAux

/-- **No square Dris index at an exponent `k ≢ 1 (mod 16)`.** -/
theorem solution (p k m s u : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk16 : k % 16 ≠ 1) (hm : Odd m)
    (hsq : s = u ^ 2) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * s) := by
  rintro ⟨h1, h2⟩
  obtain ⟨w, hw⟩ := DrisSquareAux.sigma_eq_two_mul_sq_of_square_index hm hsq h1 h2
  exact hk16
    (OddPerfectNumber.prime_and_exp_mod_sixteen_of_sigma_eq_two_mul_sq p k w hp hp4 hk4 hw).2
