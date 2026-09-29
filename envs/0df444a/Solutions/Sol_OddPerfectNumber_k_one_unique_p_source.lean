-- Prove2me | solution 1 for OddPerfectNumber.k_one_unique_p_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T08:39:31.441248+00:00
-- url     : https://prove2.me/submissions/875b1029-28cd-4261-a78f-35025988d5d2

import Mathlib

theorem solution (p m d : Nat)
    (hp : p.Prime)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hval : padicValNat p (∑ x ∈ (m ^ 2).divisors, x) = 1) :
    ∃! q ∈ (m ^ 2).primeFactors,
      p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hσ0 : (∑ x ∈ (m ^ 2).divisors, x) ≠ 0 := by
    intro h0
    rw [h0, padicValNat_zero_right] at hval
    exact zero_ne_one hval
  have hm2 : m ^ 2 ≠ 0 := by
    intro h0
    rw [h0, Nat.divisors_zero, Finset.sum_empty] at hσ0
    exact hσ0 rfl
  have hsum : (∑ x ∈ (m ^ 2).divisors, x)
      = ArithmeticFunction.sigma 1 (m ^ 2) :=
    (ArithmeticFunction.sigma_one_apply (m ^ 2)).symm
  have hprod : ArithmeticFunction.sigma 1 (m ^ 2)
      = ∏ q ∈ (m ^ 2).primeFactors,
        ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i := by
    simpa only [mul_one] using
      ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
        (k := 1) (n := m ^ 2) hm2
  have hσprod : (∑ x ∈ (m ^ 2).divisors, x)
      = ∏ q ∈ (m ^ 2).primeFactors,
        ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i :=
    hsum.trans hprod
  have hpdvd : p ∣ (∑ x ∈ (m ^ 2).divisors, x) := ⟨d, hsig⟩
  rw [hσprod] at hpdvd
  obtain ⟨q₀, hq₀mem, hq₀dvd⟩ := (hp.prime.dvd_finsetProd_iff _).mp hpdvd
  refine ⟨q₀, ⟨hq₀mem, hq₀dvd⟩, ?_⟩
  intro y hy
  rcases hy with ⟨hymem, hydvd⟩
  by_contra hne
  have hSy_dvd : (∑ i ∈ Finset.range ((m ^ 2).factorization y + 1), y ^ i)
      ∣ ∏ x ∈ (m ^ 2).primeFactors.erase q₀,
        ∑ i ∈ Finset.range ((m ^ 2).factorization x + 1), x ^ i :=
    Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hne, hymem⟩)
  have hpR : p ∣ ∏ x ∈ (m ^ 2).primeFactors.erase q₀,
      ∑ i ∈ Finset.range ((m ^ 2).factorization x + 1), x ^ i :=
    dvd_trans hydvd hSy_dvd
  have hsplit : (∑ i ∈ Finset.range ((m ^ 2).factorization q₀ + 1), q₀ ^ i)
      * ∏ x ∈ (m ^ 2).primeFactors.erase q₀,
        ∑ i ∈ Finset.range ((m ^ 2).factorization x + 1), x ^ i
      = ∏ q ∈ (m ^ 2).primeFactors,
        ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i :=
    Finset.mul_prod_erase
      (f := fun q => ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i)
      (s := (m ^ 2).primeFactors) hq₀mem
  obtain ⟨a, ha⟩ := hq₀dvd
  obtain ⟨b, hb⟩ := hpR
  have hpp : p * p ∣ (∑ x ∈ (m ^ 2).divisors, x) := by
    rw [hσprod, ← hsplit]
    exact ⟨a * b, by rw [ha, hb]; ring⟩
  have hsq : p ^ 2 ∣ (∑ x ∈ (m ^ 2).divisors, x) := by
    simpa [pow_two] using hpp
  have hle : 2 ≤ padicValNat p (∑ x ∈ (m ^ 2).divisors, x) :=
    (padicValNat_dvd_iff_le hσ0).mp hsq
  omega
