-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_b_one_D9_q4_31_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T07:51:18.372976+00:00
-- url     : https://prove2.me/submissions/a6059c3b-08d7-41b1-848c-30b075715183

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_ratio_mono_v1

theorem solution (D p sigma m a b c e q4 : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hrel : D * sigma = p * m ^ 2) (hD : D = 9) (hp_eq : p = 2 * D - 1)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hq4eq : q4 = 31)
    (ha : 3 ≤ a) (hb : b = 1) (hc : 2 ≤ c) (he : 1 ≤ e) :
    False := by
  subst hb
  subst hq4eq
  have hp17 : p = 17 := by omega
  have v3 : ∑ i ∈ Finset.range (6 + 1), 3 ^ i = 1093 := by
    norm_num [Finset.sum_range_succ]
  have v29 : ∑ i ∈ Finset.range (4 + 1), 29 ^ i = 732541 := by
    norm_num [Finset.sum_range_succ]
  have v31 : ∑ i ∈ Finset.range (2 + 1), 31 ^ i = 993 := by
    norm_num [Finset.sum_range_succ]
  have v5 : ∑ i ∈ Finset.range (2 * 1 + 1), 5 ^ i = 31 := by
    norm_num [Finset.sum_range_succ]
  have h6 : 6 ≤ 2 * a := by omega
  have h4 : 4 ≤ 2 * c := by omega
  have h2 : 2 ≤ 2 * e := by omega
  have r3 := OddPerfectNumber.geom_sum_ratio_mono_v1 3 6 (2 * a) (by norm_num) h6
  have r29 := OddPerfectNumber.geom_sum_ratio_mono_v1 29 4 (2 * c) (by norm_num) h4
  have r31 := OddPerfectNumber.geom_sum_ratio_mono_v1 31 2 (2 * e) (by norm_num) h2
  rw [v3] at r3
  rw [v29] at r29
  rw [v31] at r31
  have hf5 : (5:Nat) ^ (2 * 1) = 25 := by norm_num
  rw [hf5] at hfac
  rw [v5] at hsigma
  subst hD
  rw [hp17] at hrel hp_eq
  set S3 := (∑ i ∈ Finset.range (2*a+1), 3^i) with hS3
  set S29 := (∑ i ∈ Finset.range (2*c+1), 29^i) with hS29
  set S31 := (∑ i ∈ Finset.range (2*e+1), 31^i) with hS31
  set A := 3^(2*a) * 29^(2*c) * 31^(2*e) with hA
  set C := 3^6 * 29^4 * 31^2 with hC
  set P := 1093 * 732541 * 993 with hP
  have hE2 : 9 * 31 * (S3 * S29 * S31) = 17 * 25 * A := by
    have h1 : sigma = (S3 * S29 * S31) * 31 := by rw [hsigma]; ring
    have h2f : m ^ 2 = A * 25 := by rw [hfac]; ring
    rw [h1, h2f] at hrel
    linarith [hrel]
  have e2 : P * A ≤ (S3 * S29 * S31) * C := by
    have h := Nat.mul_le_mul (Nat.mul_le_mul r3 r29) r31
    calc P * A = (1093 * 3^(2*a)) * (732541 * 29^(2*c)) * (993 * 31^(2*e)) := by
            rw [hP, hA]; ring
      _ ≤ (S3 * 3^6) * (S29 * 29^4) * (S31 * 31^2) := h
      _ = (S3 * S29 * S31) * C := by rw [hC]; ring
  have hApos : 0 < A := by positivity
  -- chain : (17*25*C) * A ≤ (9*31*P) * A
  have hchain : (9 * 31 * P) * A ≤ (17 * 25 * C) * A := by
    calc (9 * 31 * P) * A = (9 * 31) * (P * A) := by ring
      _ ≤ (9 * 31) * ((S3 * S29 * S31) * C) := Nat.mul_le_mul le_rfl e2
      _ = C * (9 * 31 * (S3 * S29 * S31)) := by ring
      _ = C * (17 * 25 * A) := by rw [hE2]
      _ = (17 * 25 * C) * A := by ring
  have hlt : 17 * 25 * C < 9 * 31 * P := by norm_num [hC, hP]
  have hmul := mul_lt_mul_of_pos_right hlt hApos
  omega
