-- Prove2me | solution 1 for OddPerfectNumber.k_succ_shape_of_card_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T09:37:28.214904+00:00
-- url     : https://prove2.me/submissions/c704579a-c929-40e3-964a-e6536d53048a

import Mathlib

-- STAGED direct proof: k + 1 = 2 ^ a * q ^ b from the cardinality bound.
-- Every lemma name verified against pinned Mathlib (see explanation).
theorem solution (k : Nat)
    (hk1 : ((k + 1).primeFactors.erase 2).card ≤ 1) :
    ∃ a q b, q.Prime ∧ k + 1 = 2 ^ a * q ^ b := by
  have hkpos : k + 1 ≠ 0 := by omega
  have hrecon : (k + 1).factorization.prod (· ^ ·) = k + 1 :=
    Nat.prod_factorization_pow_eq_self hkpos
  have hsupp : ((k + 1).factorization).support = (k + 1).primeFactors :=
    Nat.support_factorization (k + 1)
  by_cases hempty : ((k + 1).primeFactors.erase 2) = ∅
  · -- Every prime factor of k + 1 is 2.
    have hsub : ((k + 1).factorization).support ⊆ ({2} : Finset ℕ) := by
      rw [hsupp]
      intro p hp
      by_contra hne
      simp only [Finset.mem_singleton] at hne
      have hmem : p ∈ ((k + 1).primeFactors.erase 2) :=
        Finset.mem_erase.mpr ⟨hne, hp⟩
      rw [hempty] at hmem
      exact Finset.notMem_empty p hmem
    have hprod : ((k + 1).factorization).prod (· ^ ·)
        = 2 ^ ((k + 1).factorization 2) := by
      show ∏ a ∈ ((k + 1).factorization).support, a ^ ((k + 1).factorization a)
        = 2 ^ ((k + 1).factorization 2)
      rw [Finset.prod_subset hsub]
      · exact Finset.prod_singleton _ 2
      · intro x _ hxnsup
        have hz : ((k + 1).factorization) x = 0 :=
          Finsupp.notMem_support_iff.mp hxnsup
        simp [hz]
    rw [hprod] at hrecon
    exact ⟨(k + 1).factorization 2, 3, 0, Nat.prime_three,
      by rw [hrecon]; simp⟩
  · -- Exactly one odd prime factor.
    have hne : ((k + 1).primeFactors.erase 2).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    have hcard1 : ((k + 1).primeFactors.erase 2).card = 1 := by
      have h1 : 1 ≤ ((k + 1).primeFactors.erase 2).card :=
        Finset.one_le_card.mpr hne
      omega
    obtain ⟨q₀, hq₀⟩ := Finset.card_eq_one.mp hcard1
    have hq₀S : q₀ ∈ ((k + 1).primeFactors.erase 2) := by
      rw [hq₀]
      exact Finset.mem_singleton_self q₀
    obtain ⟨hq₀ne2, hq₀mem⟩ := Finset.mem_erase.mp hq₀S
    have hq₀prime : q₀.Prime := Nat.prime_of_mem_primeFactors hq₀mem
    have hsub : ((k + 1).factorization).support ⊆ ({2, q₀} : Finset ℕ) := by
      rw [hsupp]
      intro p hp
      by_cases h2 : p = 2
      · simp [h2]
      · have hmem : p ∈ ((k + 1).primeFactors.erase 2) :=
          Finset.mem_erase.mpr ⟨h2, hp⟩
        rw [hq₀] at hmem
        simp only [Finset.mem_singleton] at hmem
        simp [hmem]
    have hprod : ((k + 1).factorization).prod (· ^ ·)
        = 2 ^ ((k + 1).factorization 2) * q₀ ^ ((k + 1).factorization q₀) := by
      show ∏ a ∈ ((k + 1).factorization).support, a ^ ((k + 1).factorization a)
        = 2 ^ ((k + 1).factorization 2) * q₀ ^ ((k + 1).factorization q₀)
      rw [Finset.prod_subset hsub]
      · exact Finset.prod_pair (Ne.symm hq₀ne2)
      · intro x _ hxnsup
        have hz : ((k + 1).factorization) x = 0 :=
          Finsupp.notMem_support_iff.mp hxnsup
        simp [hz]
    rw [hprod] at hrecon
    exact ⟨(k + 1).factorization 2, q₀, (k + 1).factorization q₀, hq₀prime,
      hrecon.symm⟩
