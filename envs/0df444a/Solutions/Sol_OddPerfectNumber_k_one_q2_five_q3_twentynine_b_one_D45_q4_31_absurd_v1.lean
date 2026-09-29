-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_b_one_D45_q4_31_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T06:33:21.03328+00:00
-- url     : https://prove2.me/submissions/997120a0-a3cc-498b-a07d-f7a3c1f12834

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_six
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_thirtyone_ge_two
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le

open OddPerfectNumber

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hD : D = 45) (hp_eq : p = 2 * D - 1) (hq4 : q4 = 31)
    (hb1 : b = 1) (ha : 3 ≤ a) (hc : 2 ≤ c) (he : 1 ≤ e) :
    False := by
  subst hq4
  have h6 : 6 ≤ 2 * a := by omega
  have h2 : 2 ≤ 2 * e := by omega
  have hn29 : 2 ≤ 2 * c := by omega
  have hb2 : 2 * b + 1 = 3 := by omega
  have hS5eq : (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) = 31 := by
    rw [hb2]; decide
  have h52b : 5 ^ (2*b) = 25 := by
    have : 2 * b = 2 := by omega
    rw [this]; norm_num
  have h3 := geom_ratio_lower_three_ge_six (2 * a) (by omega)
  have h31 := geom_ratio_lower_thirtyone_ge_two (2 * e) h2
  have hlast29 := geom_sum_last_three_terms_le 29 (2 * c) hn29
  have hpow1 : 29 ^ (2*c) = (29*29) * 29^(2*c-2) := by
    calc
      29 ^ (2*c) = 29 ^ ((2*c-2) + 2) := by congr 1 <;> omega
      _ = (29*29) * 29^(2*c-2) := by rw [pow_add]; ring
  have hpow2 : 29 ^ (2*c-1) = 29 * 29^(2*c-2) := by
    calc
      29 ^ (2*c-1) = 29 ^ ((2*c-2) + 1) := by congr 1 <;> omega
      _ = 29 * 29^(2*c-2) := by rw [pow_add]; ring
  have heq : ((29*29) + 29 + 1) * 29 ^ (2*c)
      = (29*29) * ((29*29) * 29^(2*c-2) + 29 * 29^(2*c-2) + 29^(2*c-2)) := by
    rw [hpow1]; ring
  have hlin :
      ((29*29) + 29 + 1) * 29 ^ (2*c) ≤
        (29*29) * (29 ^ (2*c) + 29 ^ (2*c-1) + 29 ^ (2*c-2)) := by
    rw [heq, ← hpow1, ← hpow2]
  have hscaled := Nat.mul_le_mul_left (29*29) hlast29
  have h29t :
      ((29*29) + 29 + 1) * 29 ^ (2*c) ≤
        (29*29) * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) := by
    calc
      ((29*29) + 29 + 1) * 29 ^ (2*c) ≤
          (29*29) * (29 ^ (2*c) + 29 ^ (2*c-1) + 29 ^ (2*c-2)) := hlin
      _ ≤ (29*29) * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) :=
        hscaled
  have e1 := Nat.mul_le_mul h3 h31
  have e2 := Nat.mul_le_mul e1 h29t
  have e3 := Nat.mul_le_mul e2 (le_refl 31)
  have e3b : 45 * (((1093 * 3 ^ (2*a)) * (993 * 31 ^ (2*e))) *
        ((((29*29) + 29 + 1) * 29 ^ (2*c))) * 31)
      ≤ 45 * (((729 * ∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
        (961 * ∑ i ∈ Finset.range (2*e + 1), 31 ^ i)) *
        (((29*29) * ∑ i ∈ Finset.range (2*c + 1), 29 ^ i)) * 31) :=
    Nat.mul_le_mul (le_refl 45) e3
  have r1 : 45 * (((1093 * 3 ^ (2*a)) * (993 * 31 ^ (2*e))) *
        ((((29*29) + 29 + 1) * 29 ^ (2*c))) * 31)
      = 1318747875705 * (3 ^ (2*a) * 31 ^ (2*e) * 29 ^ (2*c)) := by
    ring
  have r2 : 45 * (((729 * ∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
        (961 * ∑ i ∈ Finset.range (2*e + 1), 31 ^ i)) *
        (((29*29) * ∑ i ∈ Finset.range (2*c + 1), 29 ^ i)) * 31)
      = 26513033805 * sigma := by
    rw [hsigma, hS5eq]; ring
  have hLow : 1318747875705 * (3 ^ (2*a) * 31 ^ (2*e) * 29 ^ (2*c))
      ≤ 26513033805 * sigma := by
    rw [← r1, ← r2]; exact e3b
  have hp89 : p = 89 := by omega
  have hrel45 : 45 * sigma = 89 * m ^ 2 := by
    rw [← hD, ← hp89]; exact hrel
  have hm2 : m ^ 2 = 25 * (3 ^ (2*a) * 31 ^ (2*e) * 29 ^ (2*c)) := by
    rw [hfac, h52b]; ring
  have hU : 26513033805 * sigma
      = 1310922227025 * (3 ^ (2*a) * 31 ^ (2*e) * 29 ^ (2*c)) := by
    have hM : 26513033805 * sigma = 589178529 * (45 * sigma) := by ring
    rw [hM, hrel45, hm2]; ring
  have hXpos : 0 < 3 ^ (2*a) * 31 ^ (2*e) * 29 ^ (2*c) := by
    positivity
  have hle : 1318747875705 * (3 ^ (2*a) * 31 ^ (2*e) * 29 ^ (2*c))
      ≤ 1310922227025 * (3 ^ (2*a) * 31 ^ (2*e) * 29 ^ (2*c)) := by
    rw [← hU]; exact hLow
  have hLU : 1318747875705 ≤ 1310922227025 :=
    le_of_mul_le_mul_right hle hXpos
  norm_num at hLU
