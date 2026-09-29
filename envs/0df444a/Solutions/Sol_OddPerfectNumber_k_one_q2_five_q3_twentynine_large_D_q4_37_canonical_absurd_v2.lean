-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_37_canonical_absurd_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T08:59:53.696401+00:00
-- url     : https://prove2.me/submissions/27754e0d-7cf5-4978-9a59-7b1ffd0bb464

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_37_D_le_244_v2

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlow : 75 ≤ D)
    (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4eq : q4 = 37)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by
  have hDupper :=
    OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_37_D_le_244_v2
      m a b c e D p q4 sigma hfac hsigma hrel hDlow hp hp_eq hq4prime hq4eq
      ha hb hc he
  let S3 := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
  let S5 := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
  let S29 := ∑ i ∈ Finset.range (2*c + 1), 29 ^ i
  let Sq := ∑ i ∈ Finset.range (2*e + 1), q4 ^ i
  have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_eight (2*a) (by omega)
  have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_six_sharp (2*b) (by omega)
  have h29last := OddPerfectNumber.geom_sum_last_three_terms_le 29 (2*c) (by omega)
  have h29pow1 : 29 ^ (2*c - 1) = 29 ^ (2*c - 2) * 29 := by
    calc
      29 ^ (2*c - 1) = 29 ^ ((2*c - 2) + 1) := by congr 1 <;> omega
      _ = 29 ^ (2*c - 2) * 29 := by rw [pow_succ]
  have h29pow2 : 29 ^ (2*c) = 29 ^ (2*c - 1) * 29 := by
    calc
      29 ^ (2*c) = 29 ^ ((2*c - 1) + 1) := by congr 1 <;> omega
      _ = 29 ^ (2*c - 1) * 29 := by rw [pow_succ]
  have h29 : 871 * 29 ^ (2*c) ≤ 841 * S29 := by
    dsimp [S29] at h29last ⊢
    nlinarith [h29last, h29pow1, h29pow2]
  have hqlast := OddPerfectNumber.geom_sum_last_three_terms_le q4 (2*e) (by omega)
  have hqpow1 : q4 ^ (2*e - 1) = q4 ^ (2*e - 2) * q4 := by
    calc
      q4 ^ (2*e - 1) = q4 ^ ((2*e - 2) + 1) := by congr 1 <;> omega
      _ = q4 ^ (2*e - 2) * q4 := by rw [pow_succ]
  have hqpow2 : q4 ^ (2*e) = q4 ^ (2*e - 1) * q4 := by
    calc
      q4 ^ (2*e) = q4 ^ ((2*e - 1) + 1) := by congr 1 <;> omega
      _ = q4 ^ (2*e - 1) * q4 := by rw [pow_succ]
  have hq : (q4^2 + q4 + 1) * q4 ^ (2*e) ≤ q4^2 * Sq := by
    dsimp [Sq] at hqlast ⊢
    nlinarith [hqlast, hqpow1, hqpow2]
  have hmul35 := Nat.mul_le_mul h3 h5
  have h29q := Nat.mul_le_mul h29 hq
  have hmul := Nat.mul_le_mul hmul35 h29q
  have hcross :
      167410181341 * (q4^2 + q4 + 1) *
          (3^(2*a) * 5^(2*b) * 29^(2*c) * q4^(2*e)) ≤
        86215640625 * q4^2 * (S3 * S5 * S29 * Sq) := by
    calc
      167410181341 * (q4^2 + q4 + 1) *
          (3^(2*a) * 5^(2*b) * 29^(2*c) * q4^(2*e)) =
          (9841*3^(2*a)) * (19531*5^(2*b)) *
            ((871*29^(2*c)) * ((q4^2+q4+1)*q4^(2*e))) := by ring
      _ ≤ (6561*S3) * (15625*S5) * ((841*S29) * (q4^2*Sq)) := by
        simpa only [S3, S5, S29, Sq] using hmul
      _ = 86215640625 * q4^2 * (S3*S5*S29*Sq) := by ring
  have hmpos : 0 < m ^ 2 := by rw [hfac]; positivity
  have hineq :
      167410181341 * (q4^2 + q4 + 1) * D * (m^2) ≤
        86215640625 * q4^2 * p * (m^2) := by
    have hmulD := Nat.mul_le_mul_left D hcross
    calc
      167410181341 * (q4^2 + q4 + 1) * D * (m^2) =
          D * (167410181341 * (q4^2+q4+1) *
            (3^(2*a)*5^(2*b)*29^(2*c)*q4^(2*e))) := by rw [hfac]; ring
      _ ≤ D * (86215640625 * q4^2 * (S3*S5*S29*Sq)) := hmulD
      _ = 86215640625 * q4^2 * (D*sigma) := by rw [hsigma]; ring
      _ = 86215640625 * q4^2 * (p*(m^2)) := by rw [hrel]
      _ = 86215640625 * q4^2 * p * (m^2) := by ring
  rw [hq4eq, hp_eq] at hineq
  have hbound : 167410181341 * (37^2 + 37 + 1) * D ≤
      86215640625 * 37^2 * (2 * D - 1) := by
    apply Nat.le_of_mul_le_mul_right (by simpa [Nat.mul_assoc] using hineq)
    exact hmpos
  norm_num at hbound
  by_cases hD230 : D ≤ 230
  · omega
  have hcands : D = 231 ∨ D = 233 ∨ D = 235 ∨ D = 237 ∨ D = 239 ∨ D = 241 ∨ D = 243 := by
    rcases hDodd with ⟨k, hk⟩
    omega
  rcases hcands with h231 | hrest
  · have h7 : 7 ∣ D := by norm_num [h231]
    have hs := hDsupport 7 (by norm_num) h7
    norm_num [hq4eq] at hs
  rcases hrest with h233 | hrest
  · have hp' := hp; rw [hp_eq, h233] at hp'; norm_num at hp'
  rcases hrest with h235 | hrest
  · have hp' := hp; rw [hp_eq, h235] at hp'; norm_num at hp'
  rcases hrest with h237 | hrest
  · have hp' := hp; rw [hp_eq, h237] at hp'; norm_num at hp'
  rcases hrest with h239 | hrest
  · have hp' := hp; rw [hp_eq, h239] at hp'; norm_num at hp'
  rcases hrest with h241 | h243
  · have hp' := hp; rw [hp_eq, h241] at hp'; norm_num at hp'
  · have hp' := hp; rw [hp_eq, h243] at hp'; norm_num at hp'
