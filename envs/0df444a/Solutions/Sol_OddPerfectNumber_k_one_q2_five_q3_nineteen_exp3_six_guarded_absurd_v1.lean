-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_exp3_six_guarded_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T16:47:35.86498+00:00
-- url     : https://prove2.me/submissions/0ca68791-ea9b-4074-a541-828a80f04076

import Mathlib

set_option autoImplicit false

namespace FA41426FAux

theorem geom_lt (q n : ℕ) (hq : 1 ≤ q) :
    (∑ i ∈ Finset.range (n + 1), q ^ i) * (q - 1) < q ^ n * q := by
  obtain ⟨x, rfl⟩ : ∃ x, q = x + 1 := ⟨q - 1, by omega⟩
  have h := geom_sum_mul_add x (n + 1)
  rw [pow_succ] at h
  rw [Nat.add_sub_cancel, ← h]
  exact Nat.lt_succ_self _

theorem fact4 (n q : ℕ) (hn : n ≠ 0) (hq : 19 < q)
    (hsub : n.primeFactors ⊆ {3, 5, 19, q}) :
    n = 3 ^ n.factorization 3 * 5 ^ n.factorization 5 * 19 ^ n.factorization 19 *
      q ^ n.factorization q := by
  have h := Nat.prod_factorization_pow_eq_self hn
  rw [Finsupp.prod_of_support_subset _ hsub _
    (fun _ _ => pow_zero _)] at h
  rw [Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.prod_insert (by simp only [Finset.mem_singleton]; omega),
    Finset.prod_singleton] at h
  rw [← mul_assoc, ← mul_assoc] at h
  exact h.symm

theorem sigma4 (B C E q : ℕ) (hq : q.Prime) (hq19 : 19 < q) :
    ArithmeticFunction.sigma 1 (3 ^ 6 * 5 ^ B * 19 ^ C * q ^ E) =
      1093 * (∑ i ∈ Finset.range (B + 1), 5 ^ i) * (∑ i ∈ Finset.range (C + 1), 19 ^ i) *
        (∑ i ∈ Finset.range (E + 1), q ^ i) := by
  have hm := ArithmeticFunction.isMultiplicative_sigma (k := 1)
  have c3q : Nat.Coprime 3 q := (Nat.coprime_primes (by norm_num) hq).2 (by omega)
  have c5q : Nat.Coprime 5 q := (Nat.coprime_primes (by norm_num) hq).2 (by omega)
  have c19q : Nat.Coprime 19 q := (Nat.coprime_primes (by norm_num) hq).2 (by omega)
  have h1 : Nat.Coprime (3 ^ 6 * 5 ^ B * 19 ^ C) (q ^ E) :=
    Nat.Coprime.mul_left (Nat.Coprime.mul_left (Nat.Coprime.pow _ _ c3q) (Nat.Coprime.pow _ _ c5q))
      (Nat.Coprime.pow _ _ c19q)
  have h2 : Nat.Coprime (3 ^ 6 * 5 ^ B) (19 ^ C) :=
    Nat.Coprime.mul_left (Nat.Coprime.pow _ _ (by norm_num)) (Nat.Coprime.pow _ _ (by norm_num))
  have h3 : Nat.Coprime (3 ^ 6) (5 ^ B) := Nat.Coprime.pow _ _ (by norm_num)
  have h36 : ArithmeticFunction.sigma 1 (3 ^ 6) = 1093 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num)]
    simp [Finset.sum_range_succ]
  rw [hm.map_mul_of_coprime h1, hm.map_mul_of_coprime h2, hm.map_mul_of_coprime h3, h36,
    ArithmeticFunction.sigma_one_apply_prime_pow (p := 5) (by norm_num),
    ArithmeticFunction.sigma_one_apply_prime_pow (p := 19) (by norm_num),
    ArithmeticFunction.sigma_one_apply_prime_pow hq]

theorem mem_pf (m r : ℕ) (hr : r.Prime) (hm0 : m ≠ 0) (h : r ∣ m ^ 2) :
    r ∈ m.primeFactors :=
  Nat.mem_primeFactors.2 ⟨hr, hr.dvd_of_dvd_pow h, hm0⟩

end FA41426FAux

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hm0 : m ≠ 0)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4) (hq4ne : q4 ≠ 1093)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 6) :
    False := by
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero _ hm0
  have hsub : (m ^ 2).primeFactors ⊆ {3, 5, 19, q4} := by
    intro x hx
    rw [Nat.primeFactors_pow _ (by norm_num)] at hx
    rcases hsupport x hx with h | h | h | h <;> simp [h]
  have hfac0 := FA41426FAux.fact4 (m ^ 2) q4 hm2 hq4gt hsub
  rw [h3exp] at hfac0
  obtain ⟨B, C, E, hfac⟩ : ∃ B C E : ℕ, m ^ 2 = 3 ^ 6 * 5 ^ B * 19 ^ C * q4 ^ E :=
    ⟨_, _, _, hfac0⟩
  have hsum : (∑ x ∈ (m ^ 2).divisors, x) =
      1093 * (∑ i ∈ Finset.range (B + 1), 5 ^ i) * (∑ i ∈ Finset.range (C + 1), 19 ^ i) *
        (∑ i ∈ Finset.range (E + 1), q4 ^ i) := by
    rw [← ArithmeticFunction.sigma_one_apply, hfac, FA41426FAux.sigma4 B C E q4 hq4prime hq4gt]
  rw [hsum] at hsig
  have h1093 : Nat.Prime 1093 := by norm_num
  have hdiv : 1093 ∣ p * d := by
    rw [← hsig, mul_assoc, mul_assoc]
    exact dvd_mul_right _ _
  rcases (Nat.Prime.dvd_mul h1093).1 hdiv with h | h
  · have hpe : p = 1093 := ((Nat.prime_dvd_prime_iff_eq h1093 hp).1 h).symm
    subst hpe
    norm_num at hprod
    have h547 : Nat.Prime 547 := by norm_num
    have hmem := FA41426FAux.mem_pf m 547 h547 hm0 ⟨d, hprod⟩
    have hq : q4 = 547 := by
      rcases hsupport 547 hmem with h | h | h | h <;> omega
    subst hq
    have ha := FA41426FAux.geom_lt 5 B (by norm_num)
    have hb := FA41426FAux.geom_lt 19 C (by norm_num)
    have hc := FA41426FAux.geom_lt 547 E (by norm_num)
    norm_num at ha hb hc
    generalize (∑ i ∈ Finset.range (B + 1), 5 ^ i) = S5 at ha hsig
    generalize (∑ i ∈ Finset.range (C + 1), 19 ^ i) = S19 at hb hsig
    generalize (∑ i ∈ Finset.range (E + 1), 547 ^ i) = S547 at hc hsig
    generalize 5 ^ B = X at ha hfac
    generalize 19 ^ C = Y at hb hfac
    generalize 547 ^ E = W at hc hfac
    have hab : (S5 * 4) * (S19 * 18) < (X * 5) * (Y * 19) :=
      Nat.mul_lt_mul'' ha hb
    have habc : (S5 * 4) * (S19 * 18) * (S547 * 546) < (X * 5) * (Y * 19) * (W * 547) :=
      Nat.mul_lt_mul'' hab hc
    have hkey : 547 * (S5 * S19 * S547) = 729 * (X * Y * W) := by
      have e1 : 1093 * (S5 * S19 * S547) = 1093 * d := by rw [← hsig]; ring
      have e2 : S5 * S19 * S547 = d := Nat.eq_of_mul_eq_mul_left (by norm_num) e1
      rw [e2, ← hprod, hfac]; ring
    have hP : 39312 * (S5 * S19 * S547) < 51965 * (X * Y * W) := by
      have : (S5 * 4) * (S19 * 18) * (S547 * 546) = 39312 * (S5 * S19 * S547) := by ring
      have h2 : (X * 5) * (Y * 19) * (W * 547) = 51965 * (X * Y * W) := by ring
      rw [this, h2] at habc
      exact habc
    generalize S5 * S19 * S547 = P at hP hkey
    generalize X * Y * W = T at hP hkey
    omega
  · have h2 : 1093 ∣ m ^ 2 := dvd_trans h hddvd
    have hmem := FA41426FAux.mem_pf m 1093 h1093 hm0 h2
    rcases hsupport 1093 hmem with h | h | h | h <;> omega
