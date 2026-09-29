-- Prove2me | solution 1 for OddPerfectNumber.k_one_valuation_flow
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T11:11:14.061331+00:00
-- url     : https://prove2.me/submissions/0340a49a-8e44-44d2-ba2c-13ddb53a4d1c

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_diophantine_deficiency_witness

open OddPerfectNumber

-- Valuation-flow identity: the witness gives m^2 = t*d and sigma(m^2) = p*d,
-- so d unfolds over its own prime support and extends to the support of m^2
-- with trivial extra factors.
theorem solution (p m : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hpm : ¬ p ∣ m) (hm_odd : Odd m)
    (heq : (1 + p) * (∑ d ∈ (m ^ 2).divisors, d) = 2 * (p * m ^ 2)) :
    (∑ d ∈ (m ^ 2).divisors, d)
      = p * ∏ q ∈ (m ^ 2).primeFactors,
          q ^ ((m ^ 2).factorization q - ((p + 1) / 2).factorization q) := by
  obtain ⟨d, hdvd, hsig, -⟩ :=
    k_one_diophantine_deficiency_witness p m hp hp4 hpm hm_odd heq
  obtain ⟨k, hk⟩ := hm_odd
  have hm0 : m ≠ 0 := by omega
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have htpos : 0 < (p + 1) / 2 := by
    have h2 := hp.two_le
    omega
  have ht0 : (p + 1) / 2 ≠ 0 := ne_of_gt htpos
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hdvd
    exact hm2 hdvd
  have hdvd_d : d ∣ m ^ 2 := ⟨(p + 1) / 2, hdvd.trans (mul_comm _ _)⟩
  have hFm : (m ^ 2).factorization
      = ((p + 1) / 2).factorization + d.factorization := by
    rw [hdvd]
    exact Nat.factorization_mul ht0 hd0
  have hD : d.factorization
      = (m ^ 2).factorization - ((p + 1) / 2).factorization := by
    rw [hFm]
    exact (add_tsub_cancel_left _ _).symm
  have hfin : d.factorization.prod (· ^ ·)
      = ∏ q ∈ d.primeFactors, q ^ d.factorization q := by
    show (∏ a ∈ d.factorization.support, a ^ d.factorization a) = _
    rw [Nat.support_factorization]
  have hself : d.factorization.prod (· ^ ·) = d :=
    Nat.prod_factorization_pow_eq_self hd0
  have hsub : d.primeFactors ⊆ (m ^ 2).primeFactors :=
    Nat.primeFactors_mono hdvd_d hm2
  -- NOTE (remote CE 83550f96): Finset.prod_subset needs the same function
  -- on both sides, so first rewrite the small product pointwise via hD.
  have hpoint : ∀ q ∈ d.primeFactors, q ^ d.factorization q
      = q ^ ((m ^ 2).factorization q - ((p + 1) / 2).factorization q) := by
    intro q _
    have hq := congrArg (fun f : ℕ →₀ ℕ => f q) hD
    simp only [Finsupp.tsub_apply] at hq
    rw [hq]
  have hext : (∏ q ∈ d.primeFactors, q ^ d.factorization q)
      = ∏ q ∈ (m ^ 2).primeFactors,
          q ^ ((m ^ 2).factorization q - ((p + 1) / 2).factorization q) := by
    rw [Finset.prod_congr rfl hpoint]
    apply Finset.prod_subset hsub
    intro x hxmem hxnot
    have hprime : x.Prime := Nat.prime_of_mem_primeFactors hxmem
    have hnxd : ¬ x ∣ d := fun hdiv =>
      hxnot (Nat.mem_primeFactors.mpr ⟨hprime, hdiv, hd0⟩)
    have hDx0 : d.factorization x = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hnxd
    have hqx := congrArg (fun f : ℕ →₀ ℕ => f x) hD
    simp only [Finsupp.tsub_apply] at hqx
    rw [hDx0] at hqx
    have hz : (m ^ 2).factorization x - ((p + 1) / 2).factorization x = 0 :=
      hqx.symm
    rw [hz, pow_zero]
  rw [hsig]
  congr 1
  rw [← hself, hfin]
  exact hext
