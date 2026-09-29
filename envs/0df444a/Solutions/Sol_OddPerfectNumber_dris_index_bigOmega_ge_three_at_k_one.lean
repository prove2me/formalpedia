-- Prove2me | solution 1 for OddPerfectNumber.dris_index_bigOmega_ge_three_at_k_one
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-11T13:01:10.625429+00:00
-- url     : https://prove2.me/submissions/6166bd49-d55c-4b61-a007-6b0d46beee77

import Theorems.Thm_OddPerfectNumber_dris_prime_support_bound
import Theorems.Thm_OddPerfectNumber_sylvester_five_distinct_prime_factors

open Finset

/-- Peeling off the constant term of a geometric sum. -/
private lemma geom_succ (q n : ℕ) : ∑ i ∈ range (n + 1), q ^ i = q * (∑ i ∈ range n, q ^ i) + 1 := by
  rw [Finset.sum_range_succ']
  simp [Finset.mul_sum, pow_succ, mul_comm]

/-- Geometric sums mod `r`, when `p ≡ 1 [MOD r]`. -/
private lemma geom_mod (p n r : ℕ) (h : p % r = 1 % r) :
    (∑ i ∈ range n, p ^ i) % r = n % r := by
  rw [Finset.sum_nat_mod]
  have hstep : ∀ i ∈ range n, p ^ i % r = 1 % r := by
    intro i _
    rw [Nat.pow_mod, h, ← Nat.pow_mod, one_pow]
  rw [Finset.sum_congr rfl hstep]
  simp [Finset.sum_const]

/-- `σ(p^k)` as a geometric sum. -/
private lemma sigma_prime_pow (p k : ℕ) (hp : p.Prime) :
    ∑ d ∈ (p ^ k).divisors, d = ∑ i ∈ range (k + 1), p ^ i := by
  rw [Nat.sum_divisors_prime_pow hp]

/-- The divisor sum of a square, factored into its local divisor sums. -/
private lemma sigma_sq_local_prod {m : ℕ} (hm : m ≠ 0) :
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

/-- Each local divisor sum of `m²` exceeds `1`. -/
private lemma one_lt_local {m q : ℕ} (hm : m ≠ 0) (hq : q ∈ (m ^ 2).primeFactors) :
    1 < ∑ i ∈ range ((m ^ 2).factorization q + 1), q ^ i := by
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hq2 := hqp.two_le
  have hpos : (m ^ 2).factorization q ≠ 0 := by
    have := Nat.Prime.factorization_pos_of_dvd hqp (pow_ne_zero _ hm)
      (Nat.dvd_of_mem_primeFactors hq)
    omega
  have hmem : 1 ∈ range ((m ^ 2).factorization q + 1) := Finset.mem_range.mpr (by omega)
  have := Finset.single_le_sum (f := fun i => q ^ i) (fun i _ => Nat.zero_le _) hmem
  simp only [pow_one] at this
  omega

/-- A prime factor of `m²` is odd when `m` is odd. -/
private lemma prime_factor_odd {m q : ℕ} (hm : Odd m) (hq : q ∈ (m ^ 2).primeFactors) : q % 2 = 1 := by
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqm : q ∣ m ^ 2 := Nat.dvd_of_mem_primeFactors hq
  rcases hqp.eq_two_or_odd with h | h
  · subst h
    have : (2 : ℕ) ∣ m := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hqm
    rw [Nat.odd_iff] at hm
    omega
  · exact h

/-- Each local divisor sum of `m²` is odd, when `m` is odd. -/
private lemma local_odd {m q : ℕ} (hm : Odd m) (hq : q ∈ (m ^ 2).primeFactors) :
    (∑ i ∈ range ((m ^ 2).factorization q + 1), q ^ i) % 2 = 1 := by
  have hqodd : q % 2 = 1 := prime_factor_odd hm hq
  have hE : (m ^ 2).factorization q = 2 * m.factorization q := by
    rw [Nat.factorization_pow]
    simp
  rw [geom_mod q ((m ^ 2).factorization q + 1) 2 (by omega), hE]
  omega

/-- The divisor sum of an odd square is odd. -/
private lemma sigma_sq_odd {m : ℕ} (hm : Odd m) (hm0 : m ≠ 0) :
    (∑ x ∈ (m ^ 2).divisors, x) % 2 = 1 := by
  rw [sigma_sq_local_prod hm0, Finset.prod_nat_mod]
  rw [Finset.prod_congr rfl (fun q hq => local_odd hm hq)]
  simp


theorem solution (p m s : Nat) (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (h1 : 2 * m ^ 2 = (∑ d ∈ p.divisors, d) * s)
    (h2 : (∑ x ∈ (m ^ 2).divisors, x) = p * s) :
    3 ≤ s.primeFactorsList.length := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hp2 := hp.two_le
  -- the index is odd
  have hsodd : s % 2 = 1 := by
    have hsdvd : s ∣ (∑ x ∈ (m ^ 2).divisors, x) := ⟨p, by rw [h2]; ring⟩
    have hodd := sigma_sq_odd hm hm0
    have h2s : ¬ (2 ∣ s) := by
      intro hd
      have := hd.trans hsdvd
      omega
    omega
  -- `p` is odd
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · subst h
      have h3 : (∑ d ∈ (2 : ℕ).divisors, d) = 3 := by decide
      rw [h3] at h1
      omega
    · exact h
  -- `N = p·m²` is an odd perfect number
  have hcop : Nat.Coprime p (m ^ 2) :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hNpos : 0 < p * m ^ 2 := by positivity
  have hNperfect : Nat.Perfect (p * m ^ 2) := by
    rw [Nat.perfect_iff_sum_divisors_eq_two_mul hNpos, hcop.sum_divisors_mul, h2]
    rw [show (∑ d ∈ p.divisors, d) * (p * s) = ((∑ d ∈ p.divisors, d) * s) * p by ring, ← h1]
    ring
  have hNodd : Odd (p * m ^ 2) := (Nat.odd_iff.mpr hpodd).mul hm.pow
  have hNfac : (p * m ^ 2).primeFactors = {p} ∪ m.primeFactors := by
    rw [Nat.primeFactors_mul (by omega) (by positivity),
      Nat.primeFactors_pow m (by norm_num), hp.primeFactors]
  have hle : (p * m ^ 2).primeFactors.card ≤ 1 + m.primeFactors.card := by
    rw [hNfac]
    have := Finset.card_union_le ({p} : Finset ℕ) m.primeFactors
    simpa using this
  have hsyl := OddPerfectNumber.sylvester_five_distinct_prime_factors _ hNperfect hNodd
  have hcount := OddPerfectNumber.dris_prime_support_bound p 1 m s hp hm hpm
    (by rwa [pow_one]) (by rwa [pow_one])
  omega
