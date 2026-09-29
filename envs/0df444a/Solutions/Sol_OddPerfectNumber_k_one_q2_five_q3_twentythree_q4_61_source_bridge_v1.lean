-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_61_source_bridge_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T04:14:55.583594+00:00
-- url     : https://prove2.me/submissions/ee5c45eb-b091-49e7-8c1f-d22e2de74eb0

import Mathlib
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentythree_q4_61_external_131_source_v1
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentythree_q4_61_external_131_length_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_61_external_131_absurd_v2
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order
import Theorems.Thm_OddPerfectNumber_prime_not_dvd_own_sigma_prime_pow

theorem solution
    (m a b c e D p q4 sigma d : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hm0 : m ≠ 0)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 23 ∨ x = q4)
    (hq4prime : q4.Prime)
    (hb : 1 ≤ b)
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (hD : D = 549) (hp_eq : p = 1097) (hq4eq : q4 = 61) :
    False := by
  subst D
  subst p
  subst q4
  have h5pow : 5 ∣ 5 ^ (2 * b) := dvd_pow_self 5 (by omega)
  have hm5 : 5 ∣ m ^ 2 := by
    rw [hfac]
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (dvd_mul_of_dvd_right
        (dvd_mul_of_dvd_right
          (dvd_mul_of_dvd_right h5pow (3 ^ (2*a)))
          (23 ^ (2*c)))
        (61 ^ (2*e)))
  have h5mul : 5 ∣ 549 * sigma := by
    rw [hrel]
    exact dvd_mul_of_dvd_right hm5 1097
  have h5sigma : 5 ∣ sigma := by
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp h5mul with hbad | hs
    · norm_num at hbad
    · exact hs
  have horder3 : orderOf (3 : ZMod 5) = 4 := by
    apply (orderOf_eq_iff (x := (3 : ZMod 5)) (by norm_num)).2
    constructor
    · decide
    · intro n hn hnpos
      interval_cases n <;> decide
  have horder23 : orderOf (23 : ZMod 5) = 4 := by
    apply (orderOf_eq_iff (x := (23 : ZMod 5)) (by norm_num)).2
    constructor
    · decide
    · intro n hn hnpos
      interval_cases n <;> decide
  have hEven3 : Even (orderOf (3 : ZMod 5)) := by
    rw [horder3]
    exact ⟨2, by omega⟩
  have hEven23 : Even (orderOf (23 : ZMod 5)) := by
    rw [horder23]
    exact ⟨2, by omega⟩
  have h3no : ¬ 5 ∣ ∑ i ∈ Finset.range (2*a + 1), 3 ^ i :=
    OddPerfectNumber.geom_sum_not_dvd_of_even_order hEven3
  have h23no : ¬ 5 ∣ ∑ i ∈ Finset.range (2*c + 1), 23 ^ i :=
    OddPerfectNumber.geom_sum_not_dvd_of_even_order hEven23
  have h5no : ¬ 5 ∣ ∑ i ∈ Finset.range (2*b + 1), 5 ^ i := by
    exact OddPerfectNumber.prime_not_dvd_own_sigma_prime_pow 5 (2*b) (by norm_num)
  have h61 : 5 ∣ ∑ i ∈ Finset.range (2*e + 1), 61 ^ i := by
    have hprod : 5 ∣
        (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
        (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
        (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
        (∑ i ∈ Finset.range (2*e + 1), 61 ^ i) := by
      simpa [hsigma] using h5sigma
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp hprod with hleft | h61
    · rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp hleft with hleft | h23
      · rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp hleft with h3 | h5
        · exact False.elim (h3no h3)
        · exact False.elim (h5no h5)
      · exact False.elim (h23no h23)
    · exact h61
  have hlen := OddPerfectNumber.q2_five_q3_twentythree_q4_61_external_131_length_v2 e h61
  have h131local :=
    OddPerfectNumber.q2_five_q3_twentythree_q4_61_external_131_source_v1 e hlen
  have h131sigma : 131 ∣ sigma := by
    rw [hsigma]
    simpa [mul_assoc] using
      (dvd_mul_of_dvd_right
        (dvd_mul_of_dvd_right
          (dvd_mul_of_dvd_right h131local
            (∑ i ∈ Finset.range (2*c + 1), 23 ^ i))
          (∑ i ∈ Finset.range (2*b + 1), 5 ^ i))
        (∑ i ∈ Finset.range (2*a + 1), 3 ^ i))
  have h131global : 131 ∣ ∑ x ∈ (m ^ 2).divisors, x := by
    rw [← hglobal]
    exact h131sigma
  exact OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_61_external_131_absurd_v2
    1097 m d 61 hp (by norm_num) hm0 hsig hddvd hsupport hq4prime rfl h131global
