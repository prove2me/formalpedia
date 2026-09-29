-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_small_D_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T17:02:53.141136+00:00
-- url     : https://prove2.me/submissions/6f520fda-8af9-4117-a216-9104425f00f2

import Mathlib
import Theorems.Thm_OddPerfectNumber_even_orders_mod_53_q3_twentythree
import Theorems.Thm_OddPerfectNumber_even_orders_mod_53_q4_691_701_709
import Theorems.Thm_OddPerfectNumber_k_one_p53_no_local_sigma_source_general

theorem solution (sigma a b c e q4 : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), q4 ^ i))
    (hdiv : 53 ∣ sigma)
    (hq4cases : q4 = 691 ∨ q4 = 701 ∨ q4 = 709) :
    False := by
  have hq4even : Even (orderOf (q4 : ZMod 53)) := by
    rcases hq4cases with h | h | h
    · subst q4
      exact OddPerfectNumber.even_orders_mod_53_q4_691_701_709.1
    · subst q4
      exact OddPerfectNumber.even_orders_mod_53_q4_691_701_709.2.1
    · subst q4
      exact OddPerfectNumber.even_orders_mod_53_q4_691_701_709.2.2
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
  have hbase := OddPerfectNumber.even_orders_mod_53_q3_twentythree
  have h3 : ¬ orderOf (3 : ZMod 53) ∣ 2 * a + 1 := even_not_dvd_odd _ _ hbase.1
  have h5 : ¬ orderOf (5 : ZMod 53) ∣ 2 * b + 1 := even_not_dvd_odd _ _ hbase.2.1
  have h23 : ¬ orderOf (23 : ZMod 53) ∣ 2 * c + 1 := even_not_dvd_odd _ _ hbase.2.2
  have hq4 : ¬ orderOf (q4 : ZMod 53) ∣ 2 * e + 1 := even_not_dvd_odd _ _ hq4even
  exact OddPerfectNumber.k_one_p53_no_local_sigma_source_general
    sigma a b c e q4 hsigma hdiv h3 h5 h23 hq4
