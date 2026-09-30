-- Prove2me | solution 1 for TranscendenceTheory.rational_interpolation_polynomial_divisibility
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T22:32:43.990501+00:00
-- url     : https://prove2.me/submissions/5491d070-5442-4208-9cb2-fcd6cd634d27

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.LinearCombination

open PowerSeries

private lemma dvd_unit_product {R : Type*} [CommMonoid R]
    (a u v f : R) (hu : u * v = 1) : a ∣ u * f ↔ a ∣ f := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c * v, ?_⟩
    calc
      f = (u * v) * f := by rw [hu, one_mul]
      _ = (u * f) * v := by ac_rfl
      _ = a * (c * v) := by rw [hc, mul_assoc]
  · rintro ⟨c, rfl⟩
    exact ⟨u * c, by ac_rfl⟩

theorem solution
    (R : Type*) [CommRing R] (Q A : Polynomial R) (H : PowerSeries R)
    (hQ : (Q : PowerSeries R) * H = 1) (α z : R) (s : ℕ) :
    (∀ i ≤ s, PowerSeries.coeff i ((A : PowerSeries R) * H) = α * z ^ i) ↔
      Polynomial.X ^ (s + 1) ∣
        (1 - Polynomial.C z * Polynomial.X) * A - Polynomial.C α * Q := by
  let G : PowerSeries R := mk fun i => z ^ i
  let L : PowerSeries R := 1 - C z * X
  have hG : L * G = 1 := by
    ext i
    cases i with
    | zero => simp [L, G, sub_mul, mul_assoc]
    | succ i =>
      simp [L, G, sub_mul, mul_assoc, coeff_C_mul, pow_succ]
      ring
  let F : PowerSeries R := (A : PowerSeries R) * H - C α * G
  let D : PowerSeries R := L * (Q : PowerSeries R)
  let B : Polynomial R := (1 - Polynomial.C z * Polynomial.X) * A - Polynomial.C α * Q
  have hunit : D * (H * G) = 1 := by
    calc
      _ = ((Q : PowerSeries R) * H) * (L * G) := by dsimp only [D]; ring
      _ = 1 := by rw [hQ, hG, one_mul]
  have hclear : D * F = (B : PowerSeries R) := by
    dsimp only [D, F, B]
    simp only [Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_one,
      Polynomial.coe_C, Polynomial.coe_X]
    change (L * (Q : PowerSeries R)) * ((A : PowerSeries R) * H - C α * G) =
      L * (A : PowerSeries R) - C α * (Q : PowerSeries R)
    linear_combination (L * (A : PowerSeries R)) * hQ -
      (C α * (Q : PowerSeries R)) * hG
  have hleft : (∀ i ≤ s, coeff i ((A : PowerSeries R) * H) = α * z ^ i) ↔
      (X : PowerSeries R) ^ (s + 1) ∣ F := by
    simp only [X_pow_dvd_iff, F, map_sub, coeff_C_mul, G, coeff_mk,
      sub_eq_zero, Nat.lt_succ_iff]
  have hright : Polynomial.X ^ (s + 1) ∣ B ↔
      (X : PowerSeries R) ^ (s + 1) ∣ (B : PowerSeries R) := by
    rw [Polynomial.X_pow_dvd_iff, X_pow_dvd_iff]
    simp only [Polynomial.coeff_coe]
  calc
    _ ↔ (X : PowerSeries R) ^ (s + 1) ∣ F := hleft
    _ ↔ (X : PowerSeries R) ^ (s + 1) ∣ D * F :=
      (dvd_unit_product _ D (H * G) F hunit).symm
    _ ↔ (X : PowerSeries R) ^ (s + 1) ∣ (B : PowerSeries R) := by rw [hclear]
    _ ↔ _ := hright.symm
