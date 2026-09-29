-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_59_no_five_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T19:34:48.380857+00:00
-- url     : https://prove2.me/submissions/d01ae9db-c86c-47aa-8c7e-e2c535ecf7c2

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_p5_no_local_sigma_source_general
import Theorems.Thm_OddPerfectNumber_order_three_mod_five_eq_four

theorem solution (sigma a b c e : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), 59 ^ i))
    (hdiv : 5 ∣ sigma) :
    False := by
  have horder3 : orderOf (3 : ZMod 5) = 4 :=
    OddPerfectNumber.order_three_mod_five_eq_four
  have horder23 : orderOf (23 : ZMod 5) = 4 := by
    apply (orderOf_eq_iff (x := (23 : ZMod 5)) (by norm_num)).2
    constructor
    · decide
    · intro n hn hnpos
      interval_cases n <;> decide
  have horder59 : orderOf (59 : ZMod 5) = 2 := by
    apply (orderOf_eq_iff (x := (59 : ZMod 5)) (by norm_num)).2
    constructor
    · decide
    · intro n hn hnpos
      interval_cases n <;> decide
  have even_not_dvd_odd : ∀ (n t : Nat), Even n → ¬ n ∣ 2 * t + 1 := by
    intro n t hn hnd
    rcases hn with ⟨k, hk⟩
    rcases hnd with ⟨u, hu⟩
    have hu' : 2 * t + 1 = (k + k) * u := by simpa [hk] using hu
    have hu'' : 2 * t + 1 = 2 * (k * u) := by
      calc
        2 * t + 1 = (k + k) * u := hu'
        _ = 2 * (k * u) := by ring
    omega
  have h3 : ¬ orderOf (3 : ZMod 5) ∣ 2 * a + 1 := by
    rw [horder3]
    have hEven4 : Even 4 := ⟨2, by omega⟩
    exact even_not_dvd_odd 4 a hEven4
  have h23 : ¬ orderOf (23 : ZMod 5) ∣ 2 * c + 1 := by
    rw [horder23]
    have hEven4 : Even 4 := ⟨2, by omega⟩
    exact even_not_dvd_odd 4 c hEven4
  have h59 : ¬ orderOf (59 : ZMod 5) ∣ 2 * e + 1 := by
    rw [horder59]
    have hEven2 : Even 2 := ⟨1, by omega⟩
    exact even_not_dvd_odd 2 e hEven2
  exact OddPerfectNumber.k_one_p5_no_local_sigma_source_general
    sigma a b c e 23 59 hsigma hdiv h3 h23 h59
