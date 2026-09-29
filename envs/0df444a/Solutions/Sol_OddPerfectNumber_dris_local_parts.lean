-- Prove2me | solution 1 for OddPerfectNumber.dris_local_parts
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-11T19:36:03.701051+00:00
-- url     : https://prove2.me/submissions/d77244ff-410b-43fe-85c8-e54c7c2259eb

import Mathlib

open Finset

namespace DHP

/-- `σ(p^k)` as a geometric sum. -/
lemma sigma_prime_pow (p k : ℕ) (hp : p.Prime) :
    ∑ d ∈ (p ^ k).divisors, d = ∑ i ∈ range (k + 1), p ^ i := by
  rw [Nat.sum_divisors_prime_pow hp]

/-- Peeling off the constant term of a geometric sum. -/
lemma geom_succ (q n : ℕ) : ∑ i ∈ range (n + 1), q ^ i = q * (∑ i ∈ range n, q ^ i) + 1 := by
  rw [Finset.sum_range_succ']
  simp [Finset.mul_sum, pow_succ, mul_comm]

/-- Geometric sums mod `r`, when `p ≡ 1 [MOD r]`. -/
lemma geom_mod (p n r : ℕ) (h : p % r = 1 % r) :
    (∑ i ∈ range n, p ^ i) % r = n % r := by
  rw [Finset.sum_nat_mod]
  have : ∀ i ∈ range n, p ^ i % r = 1 % r := by
    intro i _
    rw [Nat.pow_mod, h, ← Nat.pow_mod, one_pow]
  rw [Finset.sum_congr rfl this]
  simp [Finset.sum_const]

end DHP

namespace DrisSupport

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
  rw [ArithmeticFunction.sigma_one_apply, DHP.sigma_prime_pow q _ hqp]

/-- Each local divisor sum of `m²` exceeds `1`. -/
lemma one_lt_local {m q : ℕ} (hm : m ≠ 0) (hq : q ∈ (m ^ 2).primeFactors) :
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
  rw [DHP.geom_mod q ((m ^ 2).factorization q + 1) 2 (by omega), hE]
  omega

/-- The divisor sum of an odd square is odd. -/
lemma sigma_sq_odd {m : ℕ} (hm : Odd m) (hm0 : m ≠ 0) :
    (∑ x ∈ (m ^ 2).divisors, x) % 2 = 1 := by
  rw [sigma_sq_local_prod hm0, Finset.prod_nat_mod]
  rw [Finset.prod_congr rfl (fun q hq => local_odd hm hq)]
  simp

end DrisSupport

namespace DrisLocalParts

/-- The `p`-free part of a product is the product of the `p`-free parts. -/
lemma ordCompl_prod {p : ℕ} (E : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ q ∈ E, f q ≠ 0) :
    ordCompl[p] (∏ q ∈ E, f q) = ∏ q ∈ E, ordCompl[p] (f q) := by
  classical
  induction E using Finset.induction_on with
  | empty => simp
  | insert a E ha ih =>
      have hfa : f a ≠ 0 := hf a (Finset.mem_insert_self _ _)
      have hrest : ∀ q ∈ E, f q ≠ 0 := fun q hq => hf q (Finset.mem_insert_of_mem hq)
      have hprod0 : (∏ q ∈ E, f q) ≠ 0 := Finset.prod_ne_zero_iff.mpr hrest
      rw [Finset.prod_insert ha, Nat.ordCompl_mul, ih hrest, Finset.prod_insert ha]

/-- The `p`-valuation of a product is the sum of the `p`-valuations. -/
lemma factorization_prod_eq_sum {p : ℕ} (E : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ q ∈ E, f q ≠ 0) :
    (∏ q ∈ E, f q).factorization p = ∑ q ∈ E, (f q).factorization p := by
  classical
  induction E using Finset.induction_on with
  | empty => simp
  | insert a E ha ih =>
      have hfa : f a ≠ 0 := hf a (Finset.mem_insert_self _ _)
      have hrest : ∀ q ∈ E, f q ≠ 0 := fun q hq => hf q (Finset.mem_insert_of_mem hq)
      have hprod0 : (∏ q ∈ E, f q) ≠ 0 := Finset.prod_ne_zero_iff.mpr hrest
      rw [Finset.prod_insert ha, Nat.factorization_mul hfa hprod0, Finset.sum_insert ha]
      simp [ih hrest]

/-- **The exact local decomposition.**  In a Dris configuration the `p`-valuations of the local
divisor sums of `m²` add up to the special exponent `k`, and their `p`-free parts multiply to
exactly the Dris index `s`. -/
theorem local_parts {p k m s : ℕ} (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s)
    (h2 : (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * s) :
    (∑ q ∈ m.primeFactors,
        (∑ i ∈ range ((m ^ 2).factorization q + 1), q ^ i).factorization p) = k ∧
      (∏ q ∈ m.primeFactors,
        ordCompl[p] (∑ i ∈ range ((m ^ 2).factorization q + 1), q ^ i)) = s := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  -- the index is odd, divides `m²`, and is prime to `p`
  have hsodd : s % 2 = 1 := by
    have hsdvd : s ∣ (∑ x ∈ (m ^ 2).divisors, x) := ⟨p ^ k, by rw [h2]; ring⟩
    have hodd := DrisSupport.sigma_sq_odd hm hm0
    have h2s : ¬ (2 ∣ s) := by
      intro hd
      have := hd.trans hsdvd
      omega
    omega
  have hs0 : s ≠ 0 := by omega
  have hsm : s ∣ m ^ 2 := by
    have hd : s ∣ 2 * m ^ 2 := ⟨_, by rw [h1]; ring⟩
    have hcop : Nat.Coprime s 2 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)).symm
    exact hcop.dvd_of_dvd_mul_left hd
  have hps : ¬ p ∣ s := fun hdvd => hpm (hp.dvd_of_dvd_pow (dvd_trans hdvd hsm))
  -- the local decomposition of `σ(m²)`
  set F : ℕ → ℕ := fun q => ∑ i ∈ range ((m ^ 2).factorization q + 1), q ^ i with hF
  have hpf : (m ^ 2).primeFactors = m.primeFactors := Nat.primeFactors_pow m (by norm_num)
  have hprod : ∏ q ∈ m.primeFactors, F q = p ^ k * s := by
    rw [hF, ← hpf, ← DrisSupport.sigma_sq_local_prod hm0, h2]
  have hFne : ∀ q ∈ m.primeFactors, F q ≠ 0 := by
    intro q hq
    have := DrisSupport.one_lt_local hm0 (hpf ▸ hq)
    simp only [hF]
    omega
  have hpk0 : (p : ℕ) ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hFact : Fact p.Prime := ⟨hp⟩
  constructor
  · -- the valuations add up to `k`
    have h := factorization_prod_eq_sum (p := p) m.primeFactors F hFne
    rw [hprod, Nat.factorization_mul hpk0 hs0] at h
    have hpks : (p ^ k).factorization p = k := by
      simp [Nat.Prime.factorization_pow hp]
    have hsf : s.factorization p = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      exact Or.inr (Or.inl hps)
    simp only [Finsupp.coe_add, Pi.add_apply, hpks, hsf, add_zero] at h
    simp only [hF] at h
    omega
  · -- the `p`-free parts multiply to `s`
    have h := ordCompl_prod (p := p) m.primeFactors F hFne
    rw [hprod, Nat.ordCompl_mul] at h
    have hpk : ordCompl[p] (p ^ k) = 1 := Nat.ordCompl_self_pow hp
    have hsc : ordCompl[p] s = s := by
      have hsf : s.factorization p = 0 := by
        rw [Nat.factorization_eq_zero_iff]
        exact Or.inr (Or.inl hps)
      simp [hsf]
    rw [hpk, hsc, one_mul] at h
    simp only [hF] at h
    exact h.symm

end DrisLocalParts


/-- **The exact local decomposition of a Dris configuration.** -/
theorem solution (p k m s : Nat) (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s)
    (h2 : (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * s) :
    (∑ q ∈ m.primeFactors,
        (∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i).factorization p) = k ∧
      (∏ q ∈ m.primeFactors,
        ordCompl[p] (∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i)) = s :=
  DrisLocalParts.local_parts hp hm hpm h1 h2
