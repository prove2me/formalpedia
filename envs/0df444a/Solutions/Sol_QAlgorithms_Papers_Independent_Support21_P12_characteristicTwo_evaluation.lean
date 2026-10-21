-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P12.characteristicTwo_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T05:02:41.916257+00:00
-- url     : https://prove2.me/submissions/95ca46ca-a3bc-4951-bbb5-322fb0e27d57

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

theorem g66h_ev_two {S : Type*} [CommRing S] {r : ℕ} (u : Fin r → S) (Y : MvPolynomial (Fin r) ℤ) :
    evalIntegral u (2 * Y) = 2 * evalIntegral u Y := by
  simp [evalIntegral]

theorem g66h_ev_add {S : Type*} [CommRing S] {r : ℕ} (u : Fin r → S) (X Y : MvPolynomial (Fin r) ℤ) :
    evalIntegral u (X + Y) = evalIntegral u X + evalIntegral u Y := by
  simp [evalIntegral]

theorem g66h_ev_mul {S : Type*} [CommRing S] {r : ℕ} (u : Fin r → S) (X Y : MvPolynomial (Fin r) ℤ) :
    evalIntegral u (X * Y) = evalIntegral u X * evalIntegral u Y := by
  simp [evalIntegral]

theorem g66h_ev_pow {S : Type*} [CommRing S] {r : ℕ} (u : Fin r → S) (a : ℕ) :
    evalIntegral u (powerSum r a) = ∑ i : Fin r, u i ^ a := by
  simp [evalIntegral, powerSum]

open QAlgorithms.Papers.Independent.Support21.P12 in
theorem solution (S : Type*) [CommRing S] [CharP S 2]
    (r : ℕ) (hr : 0 < r) (u : Fin r → S) :
    (∀ a : ℕ, 1 ≤ a →
      evalIntegral u (schurQ r a) = 0 ∧
      evalIntegral u (halfSchurQ r a) = ∑ i : Fin r, u i ^ a) ∧
    evalIntegral u (etaIntegral r 0 true) = (if Odd r then 1 else 0) ∧
    (∀ a : ℕ, 1 ≤ a → evalIntegral u (etaIntegral r a true) = ∑ i : Fin r, u i ^ a) := by
  have h2 : (2 : S) = 0 := CharTwo.two_eq_zero
  have p1 : ∀ a : ℕ, 1 ≤ a →
      evalIntegral u (schurQ r a) = 0 ∧
      evalIntegral u (halfSchurQ r a) = ∑ i : Fin r, u i ^ a := by
    intro a ha
    obtain ⟨P, hP⟩ := g66h_schur_pos r a ha
    refine ⟨by rw [hP, g66h_ev_two, h2, zero_mul], ?_⟩
    unfold halfSchurQ
    rw [hP, g66h_half_two, g66h_ev_add, g66h_ev_pow, g66h_ev_two, h2, zero_mul, add_zero]
  have hc : ((if true then 1 else -1 : ℤ) * (-1) ^ (r-1)) = 1 ∨
      ((if true then 1 else -1 : ℤ) * (-1) ^ (r-1)) = -1 := by
    rcases neg_one_pow_eq_or ℤ (r-1) with h | h <;> simp [h]
  have hneg : ((((if true then 1 else -1 : ℤ) * (-1) ^ (r-1)) : ℤ) : S) = 1 := by
    rcases neg_one_pow_eq_or ℤ (r-1) with h | h <;> simp [h, CharTwo.neg_eq]
  refine ⟨p1, ?_, fun a ha => ?_⟩
  · obtain ⟨Y, hY, h0, -⟩ := g66h_eta_num r 0 _ hc
    unfold etaIntegral
    rw [hY, g66h_half_two, h0 rfl, g66h_ev_add, (p1 1 le_rfl).1, zero_add]
    simp only [evalIntegral, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, eq_intCast]
    rcases Nat.even_or_odd r with he | he
    · have ho : Odd (r - 1) := by
        obtain ⟨k, hk⟩ := he; exact ⟨k - 1, by omega⟩
      simp [ho.neg_one_pow, Nat.not_odd_iff_even.mpr he]
    · have ho : Even (r - 1) := by
        obtain ⟨k, hk⟩ := he; exact ⟨k, by omega⟩
      simp [ho.neg_one_pow, he]
  · obtain ⟨P, hP⟩ := g66h_schur_pos r a ha
    obtain ⟨Y, hY, -, h1⟩ := g66h_eta_num r a _ hc
    unfold etaIntegral
    rw [hY, g66h_half_two, h1 P ha hP, g66h_ev_add, (p1 (a+1) (by omega)).1, zero_add, g66h_ev_mul,
      g66h_ev_add, g66h_ev_pow, g66h_ev_two, h2, zero_mul, add_zero]
    simp [evalIntegral, CharTwo.neg_eq]
