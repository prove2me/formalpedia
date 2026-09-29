-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_absurd_canonical
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T18:58:32.058362+00:00
-- url     : https://prove2.me/submissions/89912269-4384-45e1-8f6e-9761186fc7f7

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_absurd_canonical_coordinates_v1
import Theorems.Thm_OddPerfectNumber_four_support_factorization_expansion
import Theorems.Thm_OddPerfectNumber_sq_factorization_two
import Theorems.Thm_OddPerfectNumber_sigma_eq_local_prod

open OddPerfectNumber

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 800000

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : m.primeFactors = {3, 5, 19, q4})
    (hq4prime : q4.Prime) (hq4gt : 19 < q4) :
    False := by
  have hm0 : m ≠ 0 := by
    obtain ⟨t, ht⟩ := hm
    omega
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have h3neq4 : 3 ≠ q4 := by omega
  have h5neq4 : 5 ≠ q4 := by omega
  have h19neq4 : 19 ≠ q4 := by omega
  -- prime support of m ^ 2
  have hsupp2 : (m ^ 2).primeFactors = {3, 5, 19, q4} := by
    rw [Nat.primeFactors_pow m (by norm_num : (2 : Nat) ≠ 0)]
    exact hsupport
  have hmem3m : 3 ∈ m.primeFactors := by
    rw [hsupport]
    simp
  have hmem5m : 5 ∈ m.primeFactors := by
    rw [hsupport]
    simp
  have hmem19m : 19 ∈ m.primeFactors := by
    rw [hsupport]
    simp
  have hmemq4m : q4 ∈ m.primeFactors := by
    rw [hsupport]
    simp
  have hmem3 : 3 ∈ (m ^ 2).primeFactors := by
    rw [hsupp2]
    simp
  have hmem5 : 5 ∈ (m ^ 2).primeFactors := by
    rw [hsupp2]
    simp
  have hmem19 : 19 ∈ (m ^ 2).primeFactors := by
    rw [hsupp2]
    simp
  have h3exp : (m ^ 2).factorization 3 = 2 * m.factorization 3 := sq_factorization_two
  have h5exp : (m ^ 2).factorization 5 = 2 * m.factorization 5 := sq_factorization_two
  have h19exp : (m ^ 2).factorization 19 = 2 * m.factorization 19 := sq_factorization_two
  have ha : 0 < m.factorization 3 :=
    Nat.Prime.factorization_pos_of_dvd (by norm_num) hm0 (Nat.dvd_of_mem_primeFactors hmem3m)
  have hb : 0 < m.factorization 5 :=
    Nat.Prime.factorization_pos_of_dvd (by norm_num) hm0 (Nat.dvd_of_mem_primeFactors hmem5m)
  have hc : 0 < m.factorization 19 :=
    Nat.Prime.factorization_pos_of_dvd (by norm_num) hm0 (Nat.dvd_of_mem_primeFactors hmem19m)
  have he : 0 < m.factorization q4 :=
    hq4prime.factorization_pos_of_dvd hm0 (Nat.dvd_of_mem_primeFactors hmemq4m)
  -- coordinate extraction: the m ^ 2 factorisation in half exponents
  have hfac : m ^ 2 = 3 ^ (2 * m.factorization 3) * 5 ^ (2 * m.factorization 5) *
      19 ^ (2 * m.factorization 19) * q4 ^ (2 * m.factorization q4) := by
    have h := four_support_factorization_expansion (m ^ 2) 3 5 19 q4 hm20 hsupp2
      (by norm_num) (by norm_num) h3neq4 (by norm_num) h5neq4 h19neq4
    rwa [sq_factorization_two, sq_factorization_two, sq_factorization_two, sq_factorization_two] at h
  -- coordinate extraction: the local sigma product
  let sigma : Nat := (∑ i ∈ Finset.range (2 * m.factorization 3 + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * m.factorization 5 + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * m.factorization 19 + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2 * m.factorization q4 + 1), q4 ^ i)
  have hExpand :
      (∏ q ∈ ({3, 5, 19, q4} : Finset Nat),
          (∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i))
        = (∑ i ∈ Finset.range ((m ^ 2).factorization 3 + 1), 3 ^ i) *
          (∑ i ∈ Finset.range ((m ^ 2).factorization 5 + 1), 5 ^ i) *
          (∑ i ∈ Finset.range ((m ^ 2).factorization 19 + 1), 19 ^ i) *
          (∑ i ∈ Finset.range ((m ^ 2).factorization q4 + 1), q4 ^ i) := by
    rw [Finset.prod_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          omega),
      Finset.prod_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          omega),
      Finset.prod_insert (by
          simp only [Finset.mem_singleton]
          omega),
      Finset.prod_singleton]
    ac_rfl
  have hsigma : sigma = (∑ i ∈ Finset.range (2 * m.factorization 3 + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * m.factorization 5 + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * m.factorization 19 + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2 * m.factorization q4 + 1), q4 ^ i) := rfl
  have hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x := by
    rw [sigma_eq_local_prod m hm20, hsupp2, hExpand]
    rw [sq_factorization_two, sq_factorization_two, sq_factorization_two, sq_factorization_two]
  have hsup : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4 := by
    intro x hx
    rw [hsupport] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    tauto
  exact k_one_q2_five_q3_nineteen_absurd_canonical_coordinates_v1 p m d q4
    (m.factorization 3) (m.factorization 5) (m.factorization 19) (m.factorization q4) sigma
    hp hp4 hm hpm hprod hsig hsup hq4prime hq4gt
    hfac hsigma hglobal hmem3 h3exp hmem5 h5exp hmem19 h19exp ha hb hc he
