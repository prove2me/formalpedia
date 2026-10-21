-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P12.schur_integrality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:59:46.262645+00:00
-- url     : https://prove2.me/submissions/e9c84a99-b98b-44e7-b54f-7a71a7975a28

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P12
noncomputable section

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support21.P12

theorem g66h_prod {A ι : Type*} [CommRing A] [DecidableEq ι] (s : Finset ι) (g : ι → A) :
    ∃ R : A, ∏ i ∈ s, (1 + 2 * g i) = 1 + 2 * ∑ i ∈ s, g i + 4 * R := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert j s hj ih =>
    obtain ⟨R, hR⟩ := ih
    refine ⟨g j * ∑ i ∈ s, g i + R + 2 * g j * R, ?_⟩
    rw [Finset.prod_insert hj, Finset.sum_insert hj, hR]; ring

def g66h_g (r : ℕ) (i : Fin r) : PowerSeries (MvPolynomial (Fin r) ℤ) :=
  PowerSeries.mk fun a => if a = 0 then 0 else MvPolynomial.X i ^ a

theorem g66h_factor (r : ℕ) (i : Fin r) : schurFactor r i = 1 + 2 * g66h_g r i := by
  ext a
  have h2 : (2 : PowerSeries (MvPolynomial (Fin r) ℤ)) = PowerSeries.C 2 := by
    rw [map_ofNat]
  rw [h2]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [schurFactor, g66h_g, PowerSeries.coeff_mk]
  · simp [schurFactor, g66h_g, PowerSeries.coeff_mk, PowerSeries.coeff_one, ha.ne']

theorem g66h_schur0 (r : ℕ) : schurQ r 0 = 1 := by
  unfold schurQ
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_prod]
  apply Finset.prod_eq_one
  intro i _
  simp [schurFactor]

theorem g66h_schur_pos (r a : ℕ) (ha : 1 ≤ a) :
    ∃ P : MvPolynomial (Fin r) ℤ, schurQ r a = 2 * (powerSum r a + 2 * P) := by
  classical
  obtain ⟨R, hR⟩ := g66h_prod (Finset.univ : Finset (Fin r)) (g66h_g r)
  refine ⟨PowerSeries.coeff a R, ?_⟩
  have h2 : (2 : PowerSeries (MvPolynomial (Fin r) ℤ)) = PowerSeries.C 2 := by rw [map_ofNat]
  have h4 : (4 : PowerSeries (MvPolynomial (Fin r) ℤ)) = PowerSeries.C 4 := by rw [map_ofNat]
  unfold schurQ
  simp_rw [g66h_factor]
  rw [hR, h2, h4]
  simp only [map_add, PowerSeries.coeff_C_mul, map_sum, g66h_g, PowerSeries.coeff_mk,
    PowerSeries.coeff_one, powerSum]
  have : a ≠ 0 := by omega
  simp [this]; ring

theorem g66h_coeff_half {r : ℕ} (p : MvPolynomial (Fin r) ℤ) (m : Fin r →₀ ℕ) :
    (integerHalf p).coeff m = p.coeff m / 2 := rfl

theorem g66h_half_two (r : ℕ) (Y : MvPolynomial (Fin r) ℤ) : integerHalf (2 * Y) = Y := by
  ext m
  rw [g66h_coeff_half]
  have : (2 : MvPolynomial (Fin r) ℤ) = MvPolynomial.C 2 := by rw [map_ofNat]
  rw [this, MvPolynomial.coeff_C_mul]
  omega

theorem g66h_eta_num (r a : ℕ) (c : ℤ) (hc : c = 1 ∨ c = -1) :
    ∃ Y : MvPolynomial (Fin r) ℤ,
      2 * schurQ r (a+1) + MvPolynomial.C c * schurQ r a + (if a = 0 then 1 else 0) = 2 * Y ∧
      (a = 0 → Y = schurQ r 1 + MvPolynomial.C ((c + 1) / 2)) ∧
      (∀ P, 1 ≤ a → schurQ r a = 2 * (powerSum r a + 2 * P) →
        Y = schurQ r (a+1) + MvPolynomial.C c * (powerSum r a + 2 * P)) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · refine ⟨schurQ r 1 + MvPolynomial.C ((c + 1) / 2), ?_, fun _ => rfl, fun _ h => by omega⟩
    rw [g66h_schur0]
    rcases hc with rfl | rfl
    · simp; ring_nf
    · simp
  · obtain ⟨P, hP⟩ := g66h_schur_pos r a ha
    refine ⟨schurQ r (a+1) + MvPolynomial.C c * (powerSum r a + 2 * P), ?_, fun h => by omega, ?_⟩
    · rw [hP, if_neg (by omega)]; ring
    · intro P' _ hP'
      have : powerSum r a + 2 * P = powerSum r a + 2 * P' := by
        have h2 : (2 : MvPolynomial (Fin r) ℤ) ≠ 0 := by
          rw [show (2 : MvPolynomial (Fin r) ℤ) = MvPolynomial.C 2 by rw [map_ofNat]]
          simp
        exact mul_left_cancel₀ h2 (hP.symm.trans hP')
      rw [this]

open QAlgorithms.Papers.Independent.Support21.P12 in
theorem solution (r : ℕ) (hr : 0 < r) :
    schurQ r 0 = 1 ∧
    (∀ a : ℕ, 1 ≤ a → ∃ p : MvPolynomial (Fin r) ℤ,
      schurQ r a - 2 * powerSum r a = 4 * p) ∧
    (∀ a : ℕ, ∀ plus : Bool,
      MvPolynomial.map (Int.castRingHom ℚ) (etaIntegral r a plus) = etaRational r a plus) := by
  refine ⟨g66h_schur0 r, fun a ha => ?_, fun a plus => ?_⟩
  · obtain ⟨P, hP⟩ := g66h_schur_pos r a ha
    exact ⟨P, by rw [hP]; ring⟩
  · have hc : ((if plus then 1 else -1 : ℤ) * (-1) ^ (r-1)) = 1 ∨
        ((if plus then 1 else -1 : ℤ) * (-1) ^ (r-1)) = -1 := by
      rcases neg_one_pow_eq_or ℤ (r-1) with h | h <;> cases plus <;> simp [h]
    obtain ⟨Y, hY, h0, h1⟩ := g66h_eta_num r a _ hc
    unfold etaIntegral etaRational
    rw [hY, g66h_half_two]
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rw [h0 rfl, g66h_schur0]
      simp only [map_add, MvPolynomial.map_C, map_one, if_true, mul_one]
      rw [add_assoc, ← map_add]
      congr 2
      rcases Nat.even_or_odd (r-1) with he | he <;> cases plus <;> simp [he.neg_one_pow] <;> norm_num
    · obtain ⟨P, hP⟩ := g66h_schur_pos r a ha
      rw [h1 P ha hP, hP, if_neg (show a ≠ 0 by omega)]
      simp only [map_add, map_mul, MvPolynomial.map_C, add_zero]
      have h2 : (MvPolynomial.map (Int.castRingHom ℚ) (2 : MvPolynomial (Fin r) ℤ)) =
          MvPolynomial.C 2 := by rw [map_ofNat, map_ofNat]
      rw [h2]
      have key : (MvPolynomial.C ((Int.castRingHom ℚ) (if plus then 1 else -1 : ℤ)) *
          MvPolynomial.C ((Int.castRingHom ℚ) ((-1) ^ (r-1))) :
          MvPolynomial (Fin r) ℚ) = MvPolynomial.C ((if plus then 1 else -1 : ℚ) * (-1) ^ (r-1) / 2) *
            MvPolynomial.C 2 := by
        simp only [← map_mul]; congr 1; cases plus <;> simp <;> ring
      rw [key]; ring
