-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P16.vacuumTransforms
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T16:34:34.322979+00:00
-- url     : https://prove2.me/submissions/83ed6a25-c06d-4ba4-be1e-04909d829b0a

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P16
noncomputable section

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration)

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass)

open scoped BigOperators ENNReal ComplexOrder

open QAlgorithms.Papers.Independent.Next46.P16

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P16.canonicalComplexCalculus

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P16.canonicalRealCalculus

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P16.canonicalRealNonUnitalCalculus

open Real in
theorem g62g_vw (n : ℕ) (q : Configuration n) :
    vacuumWave n q = ((π ^ (-(n : ℝ) / 4) : ℝ) : ℂ) * Complex.exp (-(∑ i, ((q i : ℂ)) ^ 2) / 2) := by
  simp only [vacuumWave, Real.rpow_eq_pow]
  push_cast
  rfl

theorem g62g_rp (n : ℕ) :
    ((Real.pi ^ (-(n : ℝ) / 4) : ℝ) : ℂ) * ((Real.pi ^ (-(n : ℝ) / 4) : ℝ) : ℂ) =
      ((Real.pi ^ (-(n : ℝ) / 2) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul, ← Real.rpow_add Real.pi_pos]
  congr 2; ring

theorem g62g_star (n : ℕ) (q : Configuration n) : star (vacuumWave n q) = vacuumWave n q := by
  simp only [vacuumWave]
  exact Complex.conj_ofReal _

theorem g62g_cpow (n : ℕ) (b : ℝ) (hb : 0 < b) :
    ((Real.pi : ℂ) / (b : ℂ)) ^ ((Fintype.card (Fin n) : ℂ) / 2) =
      (((Real.pi / b) ^ ((n : ℝ) / 2) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow (div_nonneg Real.pi_pos.le hb.le)]
  push_cast
  simp

theorem g62g_char (n : ℕ) (q p : Configuration n) :
    rankOneCharacteristic (vacuumWave n) (vacuumWave n) q p =
        ((Real.exp (-((∑ i, q i ^ 2) + (∑ i, p i ^ 2)) / 4) : ℝ) : ℂ) := by
  unfold rankOneCharacteristic
  have hint : ∀ u : Configuration n,
      star (vacuumWave n u) *
        Complex.exp (Complex.I * ((∑ i, p i * u i) - (∑ i, q i * p i) / 2 : ℝ)) *
        vacuumWave n (u - q) =
      (((Real.pi ^ (-(n : ℝ) / 2) : ℝ) : ℂ) *
          Complex.exp (-(∑ i, ((q i : ℂ)) ^ 2) / 2 - Complex.I * (∑ i, (q i : ℂ) * p i) / 2)) *
        Complex.exp (-1 * ∑ i, ((u i : ℂ)) ^ 2 + ∑ i, ((q i : ℂ) + Complex.I * p i) * u i) := by
    intro u
    rw [g62g_star, g62g_vw, g62g_vw, ← g62g_rp]
    calc _ = ((Real.pi ^ (-(n : ℝ) / 4) : ℝ) : ℂ) * ((Real.pi ^ (-(n : ℝ) / 4) : ℝ) : ℂ) *
          (Complex.exp (-(∑ i, ((u i : ℂ)) ^ 2) / 2 +
            Complex.I * ((∑ i, p i * u i) - (∑ i, q i * p i) / 2 : ℝ) +
            -(∑ i, (((u - q) i : ℝ) : ℂ) ^ 2) / 2)) := by
          rw [Complex.exp_add, Complex.exp_add]; ring
      _ = _ := by
          rw [mul_assoc _ (Complex.exp _) (Complex.exp _), ← Complex.exp_add]
          congr 2
          simp only [Pi.sub_apply]
          push_cast
          simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib,
            ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
  simp_rw [hint]
  rw [MeasureTheory.integral_const_mul,
    GaussianFourier.integral_cexp_neg_mul_sum_add (b := 1) (by simp)]
  have h1 : ((Real.pi : ℂ) / 1) = ((Real.pi : ℂ) / ((1 : ℝ) : ℂ)) := by simp
  rw [h1, g62g_cpow n 1 one_pos, div_one]
  calc _ = (((Real.pi ^ (-(n : ℝ) / 2) * Real.pi ^ ((n : ℝ) / 2) : ℝ) : ℂ)) *
        (Complex.exp (-(∑ i, ((q i : ℂ)) ^ 2) / 2 - Complex.I * (∑ i, (q i : ℂ) * p i) / 2 +
          (∑ i, ((q i : ℂ) + Complex.I * p i) ^ 2) / (4 * ((1 : ℝ) : ℂ)))) := by
        rw [Complex.exp_add]; push_cast; ring
    _ = _ := by
        rw [← Real.rpow_add Real.pi_pos]
        rw [show -(n : ℝ) / 2 + (n : ℝ) / 2 = 0 by ring, Real.rpow_zero]
        push_cast
        rw [one_mul]
        congr 1
        simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib,
          ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        linear_combination ((p i : ℂ)) ^ 2 / 4 * Complex.I_sq

theorem g62g_two (n : ℕ) :
    Real.pi ^ (-(n : ℝ) / 2) * (Real.pi / (1 / 4)) ^ ((n : ℝ) / 2) = 2 ^ n := by
  rw [show Real.pi / (1 / 4) = 4 * Real.pi by ring,
    Real.mul_rpow (by norm_num) Real.pi_pos.le]
  rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  rw [show (2 : ℝ) * ((n : ℝ) / 2) = (n : ℝ) by ring, Real.rpow_natCast]
  have : Real.pi ^ (-(n : ℝ) / 2) * Real.pi ^ ((n : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add Real.pi_pos, show -(n : ℝ) / 2 + (n : ℝ) / 2 = 0 by ring,
      Real.rpow_zero]
  calc _ = (Real.pi ^ (-(n : ℝ) / 2) * Real.pi ^ ((n : ℝ) / 2)) * 2 ^ n := by ring
    _ = _ := by rw [this, one_mul]

theorem g62g_wig (n : ℕ) (q p : Configuration n) :
    rankOneWigner (vacuumWave n) (vacuumWave n) q p =
        (((2 : ℝ) ^ n * Real.exp (-((∑ i, q i ^ 2) + (∑ i, p i ^ 2))) : ℝ) : ℂ) := by
  unfold rankOneWigner
  have hint : ∀ y : Configuration n,
      Complex.exp (Complex.I * ((∑ i, y i * p i : ℝ) : ℂ)) *
        star (vacuumWave n (q + (1 / 2 : ℝ) • y)) * vacuumWave n (q - (1 / 2 : ℝ) • y) =
      (((Real.pi ^ (-(n : ℝ) / 2) : ℝ) : ℂ) * Complex.exp (-(∑ i, ((q i : ℂ)) ^ 2))) *
        Complex.exp (-((1 / 4 : ℝ) : ℂ) * ∑ i, ((y i : ℂ)) ^ 2 +
          ∑ i, (Complex.I * p i) * y i) := by
    intro y
    rw [g62g_star, g62g_vw, g62g_vw, ← g62g_rp]
    calc _ = ((Real.pi ^ (-(n : ℝ) / 4) : ℝ) : ℂ) * ((Real.pi ^ (-(n : ℝ) / 4) : ℝ) : ℂ) *
          (Complex.exp (Complex.I * ((∑ i, y i * p i : ℝ) : ℂ) +
            -(∑ i, (((q + (1 / 2 : ℝ) • y) i : ℝ) : ℂ) ^ 2) / 2 +
            -(∑ i, (((q - (1 / 2 : ℝ) • y) i : ℝ) : ℂ) ^ 2) / 2)) := by
          rw [Complex.exp_add, Complex.exp_add]; ring
      _ = _ := by
          rw [mul_assoc _ (Complex.exp _) (Complex.exp _), ← Complex.exp_add]
          congr 2
          simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          push_cast
          simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib,
            ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
  simp_rw [hint]
  rw [MeasureTheory.integral_const_mul,
    GaussianFourier.integral_cexp_neg_mul_sum_add (b := ((1 / 4 : ℝ) : ℂ)) (by norm_num)]
  rw [g62g_cpow n (1 / 4) (by norm_num)]
  calc _ = (((Real.pi ^ (-(n : ℝ) / 2) * (Real.pi / (1 / 4)) ^ ((n : ℝ) / 2) : ℝ) : ℂ)) *
        (Complex.exp (-(∑ i, ((q i : ℂ)) ^ 2) +
          (∑ i, (Complex.I * p i) ^ 2) / (4 * ((1 / 4 : ℝ) : ℂ)))) := by
        rw [Complex.exp_add]; push_cast; ring
    _ = _ := by
        rw [g62g_two]
        push_cast
        congr 1
        congr 1
        simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib,
          ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        linear_combination ((p i : ℂ)) ^ 2 * Complex.I_sq

theorem solution (n : ℕ) (hn : 0 < n) :
    (∀ q qr : Configuration n,
      rankOneKernel (vacuumWave n) (vacuumWave n) q qr =
        ((Real.rpow Real.pi (-(n : ℝ) / 2) *
          Real.exp (-((∑ i, q i ^ 2) + (∑ i, qr i ^ 2)) / 2) : ℝ) : ℂ)) ∧
    (∀ q p : Configuration n,
      rankOneCharacteristic (vacuumWave n) (vacuumWave n) q p =
        ((Real.exp (-((∑ i, q i ^ 2) + (∑ i, p i ^ 2)) / 4) : ℝ) : ℂ)) ∧
    (∀ q p : Configuration n,
      rankOneWigner (vacuumWave n) (vacuumWave n) q p =
        (((2 : ℝ) ^ n * Real.exp (-((∑ i, q i ^ 2) + (∑ i, p i ^ 2))) : ℝ) : ℂ)) := by
  refine ⟨fun q qr => ?_, g62g_char n, g62g_wig n⟩
  unfold rankOneKernel
  rw [g62g_star]
  simp only [vacuumWave, Real.rpow_eq_pow]
  rw [← Complex.ofReal_mul]
  congr 1
  calc _ = (Real.pi ^ (-(n : ℝ) / 4) * Real.pi ^ (-(n : ℝ) / 4)) *
      (Real.exp (-(∑ i, q i ^ 2) / 2) * Real.exp (-(∑ i, qr i ^ 2) / 2)) := by ring
    _ = _ := by
      rw [← Real.rpow_add Real.pi_pos, ← Real.exp_add]
      congr 2 <;> ring
