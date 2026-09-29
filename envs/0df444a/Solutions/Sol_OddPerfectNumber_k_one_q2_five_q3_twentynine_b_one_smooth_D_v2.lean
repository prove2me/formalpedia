-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_b_one_smooth_D_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T07:11:27.627951+00:00
-- url     : https://prove2.me/submissions/765fef04-218a-44da-a725-47cddbaf1b1e

import Mathlib

theorem solution (D m q4 : Nat)
    (hlt : D < 107) (hDpos : 0 < D) (hmpos : 0 < m) (hDm : D ∣ m ^ 2)
    (hsup : ∀ x ∈ (m ^ 2).primeFactors, x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4)
    (hq4 : q4 = 31) :
    D ∣ 1820475 := by
  subst hq4
  have hm2pos : 0 < m ^ 2 := pow_pos hmpos 2
  have hmem : ∀ p : ℕ, p.Prime → p ∣ D → p = 3 ∨ p = 5 ∨ p = 29 ∨ p = 31 := by
    intro p hp hpd
    have h1 : p ∣ m ^ 2 := dvd_trans hpd hDm
    have hne : m ^ 2 ≠ 0 := ne_of_gt hm2pos
    have hmem2 : p ∈ (m ^ 2).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, h1, hne⟩
    exact hsup p hmem2
  have f3 : D.factorization 3 ≤ 4 := by
    by_contra h
    push_neg at h
    have hdvd : (3:ℕ)^5 ∣ D :=
      calc (3:ℕ)^5 ∣ 3 ^ (D.factorization 3) := pow_dvd_pow 3 (by omega)
        _ ∣ D := Nat.ordProj_dvd D 3
    have hle : 243 ≤ D := by
      have h243 : (3:ℕ)^5 = 243 := by norm_num
      rw [h243] at hdvd
      exact Nat.le_of_dvd hDpos hdvd
    omega
  have f5 : D.factorization 5 ≤ 2 := by
    by_contra h
    push_neg at h
    have hdvd : (5:ℕ)^3 ∣ D :=
      calc (5:ℕ)^3 ∣ 5 ^ (D.factorization 5) := pow_dvd_pow 5 (by omega)
        _ ∣ D := Nat.ordProj_dvd D 5
    have hle : 125 ≤ D := by
      have h125 : (5:ℕ)^3 = 125 := by norm_num
      rw [h125] at hdvd
      exact Nat.le_of_dvd hDpos hdvd
    omega
  have f29 : D.factorization 29 ≤ 1 := by
    by_contra h
    push_neg at h
    have hdvd : (29:ℕ)^2 ∣ D :=
      calc (29:ℕ)^2 ∣ 29 ^ (D.factorization 29) := pow_dvd_pow 29 (by omega)
        _ ∣ D := Nat.ordProj_dvd D 29
    have hle : 841 ≤ D := by
      have h841 : (29:ℕ)^2 = 841 := by norm_num
      rw [h841] at hdvd
      exact Nat.le_of_dvd hDpos hdvd
    omega
  have f31 : D.factorization 31 ≤ 1 := by
    by_contra h
    push_neg at h
    have hdvd : (31:ℕ)^2 ∣ D :=
      calc (31:ℕ)^2 ∣ 31 ^ (D.factorization 31) := pow_dvd_pow 31 (by omega)
        _ ∣ D := Nat.ordProj_dvd D 31
    have hle : 961 ≤ D := by
      have h961 : (31:ℕ)^2 = 961 := by norm_num
      rw [h961] at hdvd
      exact Nat.le_of_dvd hDpos hdvd
    omega
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have fother : ∀ p : ℕ, p ≠ 3 → p ≠ 5 → p ≠ 29 → p ≠ 31 →
      D.factorization p = 0 := by
    intro p h3 h5 h29 h31
    by_cases hpp : p.Prime
    · by_contra h
      push_neg at h
      have h1 : 1 ≤ D.factorization p := by omega
      have hdvd : p ∣ D :=
        calc p = p^1 := by ring
          _ ∣ p ^ (D.factorization p) := pow_dvd_pow p h1
          _ ∣ D := Nat.ordProj_dvd D p
      have hdisj := hmem p hpp hdvd
      rcases hdisj with rfl | rfl | rfl | rfl
      · exact absurd rfl h3
      · exact absurd rfl h5
      · exact absurd rfl h29
      · exact absurd rfl h31
    · by_contra hne
      have hmem2 : p ∈ D.primeFactors := by
        rw [← Nat.support_factorization D]
        exact Finsupp.mem_support_iff.mpr hne
      exact hpp ((Nat.mem_primeFactors.mp hmem2).1)
  have e3 : ((3^4*5^2*29*31 : ℕ)).factorization 3 = 4 := by
    have g1 : ((3:ℕ)^4).factorization 3 = 4 := Nat.factorization_pow_self (by norm_num)
    have g2 : ((5:ℕ)^2).factorization 3 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    have g3 : ((29:ℕ)).factorization 3 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    have g4 : ((31:ℕ)).factorization 3 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    rw [Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul (by positivity) (by positivity),
      Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply, g1, g2, g3, g4]
  have e5 : ((3^4*5^2*29*31 : ℕ)).factorization 5 = 2 := by
    have g1 : ((3:ℕ)^4).factorization 5 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    have g2 : ((5:ℕ)^2).factorization 5 = 2 := Nat.factorization_pow_self (by norm_num)
    have g3 : ((29:ℕ)).factorization 5 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    have g4 : ((31:ℕ)).factorization 5 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    rw [Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul (by positivity) (by positivity),
      Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply, g1, g2, g3, g4]
  have e29 : ((3^4*5^2*29*31 : ℕ)).factorization 29 = 1 := by
    have g1 : ((3:ℕ)^4).factorization 29 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    have g2 : ((5:ℕ)^2).factorization 29 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    have g3 : ((29:ℕ)).factorization 29 = 1 := by
      rw [← pow_one 29]; exact Nat.factorization_pow_self (by norm_num)
    have g4 : ((31:ℕ)).factorization 29 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    rw [Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul (by positivity) (by positivity),
      Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply, g1, g2, g3, g4]
  have e31 : ((3^4*5^2*29*31 : ℕ)).factorization 31 = 1 := by
    have g1 : ((3:ℕ)^4).factorization 31 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    have g2 : ((5:ℕ)^2).factorization 31 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    have g3 : ((29:ℕ)).factorization 31 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    have g4 : ((31:ℕ)).factorization 31 = 1 := by
      rw [← pow_one 31]; exact Nat.factorization_pow_self (by norm_num)
    rw [Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul (by positivity) (by positivity),
      Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply, g1, g2, g3, g4]
  have hN : (1820475 : ℕ) = 3^4*5^2*29*31 := by norm_num
  rw [hN]
  have hNne : (3^4*5^2*29*31 : ℕ) ≠ 0 := by positivity
  rw [← Nat.factorization_le_iff_dvd hDne hNne]
  rw [Finsupp.le_iff]
  intro p _
  by_cases h3 : p = 3
  · subst h3; rw [e3]; exact f3
  · by_cases h5 : p = 5
    · subst h5; rw [e5]; exact f5
    · by_cases h29 : p = 29
      · subst h29; rw [e29]; exact f29
      · by_cases h31 : p = 31
        · subst h31; rw [e31]; exact f31
        · rw [fother p h3 h5 h29 h31]; exact Nat.zero_le _
