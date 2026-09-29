-- Prove2me | solution 1 for OddPerfectNumber.dris_prime_support_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-11T12:54:27.573478+00:00
-- url     : https://prove2.me/submissions/468181b3-ec4b-4bf9-a576-2b80d5369e08

import Mathlib

open Finset

/-- `σ(p^k)` as a geometric sum. -/
private lemma sigma_prime_pow (p k : ℕ) (hp : p.Prime) :
    ∑ d ∈ (p ^ k).divisors, d = ∑ i ∈ range (k + 1), p ^ i := by
  rw [Nat.sum_divisors_prime_pow hp]

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




/-- `Ω` is monotone under divisibility. -/
private lemma bigOmega_mono {a b : ℕ} (hb : b ≠ 0) (h : a ∣ b) :
    a.primeFactorsList.length ≤ b.primeFactorsList.length := by
  obtain ⟨c, rfl⟩ := h
  have ha : a ≠ 0 := by rintro rfl; simp at hb
  have hc : c ≠ 0 := by rintro rfl; simp at hb
  have := ArithmeticFunction.cardFactors_mul (m := a) (n := c) ha hc
  simp only [ArithmeticFunction.cardFactors_apply] at this
  omega

/-- A product of `E.card` factors each exceeding `1` has at least `E.card` prime factors,
counted with multiplicity. -/
private lemma card_le_bigOmega_prod (f : ℕ → ℕ) :
    ∀ (E : Finset ℕ), (∀ q ∈ E, 1 < f q) →
      E.card ≤ (∏ q ∈ E, f q).primeFactorsList.length := by
  intro E
  induction E using Finset.induction_on with
  | empty => intro _; simp
  | insert a E ha ih =>
      intro hf
      have hfa : 1 < f a := hf a (Finset.mem_insert_self _ _)
      have hrest : ∀ q ∈ E, 1 < f q := fun q hq => hf q (Finset.mem_insert_of_mem hq)
      have hprod0 : (∏ q ∈ E, f q) ≠ 0 := by
        refine Finset.prod_ne_zero_iff.mpr ?_
        intro q hq
        have := hrest q hq
        omega
      have hfa0 : f a ≠ 0 := by omega
      have hlen := ArithmeticFunction.cardFactors_mul (m := f a) (n := ∏ q ∈ E, f q) hfa0 hprod0
      simp only [ArithmeticFunction.cardFactors_apply] at hlen
      have hfa1 : 1 ≤ (f a).primeFactorsList.length := by
        have hpos : 0 < ArithmeticFunction.cardFactors (f a) :=
          ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hfa
        rw [ArithmeticFunction.cardFactors_apply] at hpos
        omega
      have := ih hrest
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, hlen]
      omega

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

/-- **Main counting bound.**  For a Dris configuration `2m² = σ(p^k)·s`, `σ(m²) = p^k·s`
with `p` prime, `m` odd and `p ∤ m`, the number of distinct primes dividing `m` is at most
`k + Ω(s)`. -/
theorem solution (p k m s : ℕ) (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s)
    (h2 : (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * s) :
    m.primeFactors.card ≤ k + s.primeFactorsList.length := by
  have hp2 := hp.two_le
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero _ hm0
  -- the index is odd, hence divides `m²`, hence is prime to `p`
  have hsodd : s % 2 = 1 := by
    have hsdvd : s ∣ (∑ x ∈ (m ^ 2).divisors, x) := ⟨p ^ k, by rw [h2]; ring⟩
    have hodd := sigma_sq_odd hm hm0
    have h2s : ¬ (2 ∣ s) := by
      intro hd
      have := hd.trans hsdvd
      omega
    omega
  have hs0 : s ≠ 0 := by omega
  have hsm : s ∣ m ^ 2 := by
    have hd : s ∣ 2 * m ^ 2 := ⟨_, by rw [h1]; ring⟩
    have hcop : Nat.Coprime s 2 :=
      (((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)).symm)
    exact hcop.dvd_of_dvd_mul_left hd
  have hps : ¬ p ∣ s := by
    intro hdvd
    exact hpm (hp.dvd_of_dvd_pow (dvd_trans hdvd hsm))
  -- the local decomposition of `σ(m²)`
  set F : ℕ → ℕ := fun q => ∑ i ∈ range ((m ^ 2).factorization q + 1), q ^ i with hF
  have hprod : ∏ q ∈ (m ^ 2).primeFactors, F q = p ^ k * s := by
    rw [hF, ← sigma_sq_local_prod hm0, h2]
  have hF1 : ∀ q ∈ (m ^ 2).primeFactors, 1 < F q := fun q hq => one_lt_local hm0 hq
  classical
  set S : Finset ℕ := (m ^ 2).primeFactors.filter (fun q => p ∣ F q) with hS
  set E : Finset ℕ := (m ^ 2).primeFactors.filter (fun q => ¬ p ∣ F q) with hE
  have hcards : S.card + E.card = (m ^ 2).primeFactors.card := by
    rw [hS, hE]
    exact Finset.card_filter_add_card_filter_not _
  -- the `p`-sources: at most `k` of them
  have hSk : S.card ≤ k := by
    have hdvd : p ^ S.card ∣ ∏ q ∈ S, F q := by
      calc p ^ S.card = ∏ _q ∈ S, p := by rw [Finset.prod_const]
        _ ∣ ∏ q ∈ S, F q := by
            refine Finset.prod_dvd_prod_of_dvd _ _ ?_
            intro q hq
            exact (Finset.mem_filter.mp hq).2
    have hsub : S ⊆ (m ^ 2).primeFactors := Finset.filter_subset _ _
    have hdvd2 : p ^ S.card ∣ p ^ k * s :=
      hdvd.trans (hprod ▸ Finset.prod_dvd_prod_of_subset _ _ _ hsub)
    have hcop : Nat.Coprime (p ^ S.card) s :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hps)
    have hpk : p ^ S.card ∣ p ^ k := hcop.dvd_of_dvd_mul_right hdvd2
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hpk
  -- the remaining primes: at most `Ω(s)` of them
  have hEs : E.card ≤ s.primeFactorsList.length := by
    have hsub : E ⊆ (m ^ 2).primeFactors := Finset.filter_subset _ _
    have hdvd : (∏ q ∈ E, F q) ∣ p ^ k * s :=
      hprod ▸ Finset.prod_dvd_prod_of_subset _ _ _ hsub
    have hnp : ¬ p ∣ ∏ q ∈ E, F q := by
      intro hdvd'
      obtain ⟨q, hq, hq'⟩ := (Prime.dvd_finset_prod_iff hp.prime F).mp hdvd'
      exact (Finset.mem_filter.mp hq).2 hq'
    have hcop : Nat.Coprime (∏ q ∈ E, F q) (p ^ k) :=
      Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnp).symm
    have hdvds : (∏ q ∈ E, F q) ∣ s := hcop.dvd_of_dvd_mul_left hdvd
    have hcard := card_le_bigOmega_prod F E (fun q hq => hF1 q (hsub hq))
    exact hcard.trans (bigOmega_mono hs0 hdvds)
  have hpf : (m ^ 2).primeFactors = m.primeFactors := Nat.primeFactors_pow m (by norm_num)
  rw [← hpf]
  omega

