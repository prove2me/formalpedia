-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P30.youngBound_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T06:15:06.745897+00:00
-- url     : https://prove2.me/submissions/73fe8ae6-c14b-44ed-84f1-8b4ce18997d9

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P30

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal NNReal ComplexOrder Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Claimed50.P30

lemma X7A14_phiMinus_pos {p x : ℝ} (hp : 0 < p) (hx : 1 ≤ x) : 0 < phiMinus p x := by
  unfold phiMinus
  simp only [Real.rpow_eq_pow]
  have : (x - 1) ^ p < (x + 1) ^ p :=
    Real.rpow_lt_rpow (by linarith) (by linarith) hp
  linarith

lemma X7A14_phiPlus_pos {p x : ℝ} (hx : 1 ≤ x) : 0 < phiPlus p x := by
  unfold phiPlus
  simp only [Real.rpow_eq_pow]
  have h1 : 0 < (x + 1) ^ p := Real.rpow_pos_of_pos (by linarith) p
  have h2 : 0 ≤ (x - 1) ^ p := Real.rpow_nonneg (by linarith) p
  linarith

lemma X7A14_D {p x : ℝ} (hx : 1 ≤ x) :
    Real.rpow (x + 1) (2 * p) - Real.rpow (x - 1) (2 * p) = phiPlus p x * phiMinus p x := by
  unfold phiPlus phiMinus
  simp only [Real.rpow_eq_pow]
  have e1 : (x + 1) ^ (2 * p) = ((x + 1) ^ p) ^ 2 := by
    rw [mul_comm, Real.rpow_mul (by linarith)]; norm_cast
  have e2 : (x - 1) ^ (2 * p) = ((x - 1) ^ p) ^ 2 := by
    rw [mul_comm, Real.rpow_mul (by linarith)]; norm_cast
  rw [e1, e2]; ring

lemma X7A14_pointwise {n : ℕ} (hn : 0 < n) (alpha beta : Fin n → ℝ)
    (ha : ∀ k, 1 ≤ alpha k) (hb : ∀ k, 1 ≤ beta k) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    minkowskiFunction alpha beta s ≤ youngFunction alpha beta s := by
  have hs1' : 0 < 1 - s := by linarith
  set P : Fin n → ℝ := fun k => phiPlus s (alpha k) * phiMinus s (alpha k) *
    (phiPlus (1 - s) (beta k) * phiMinus (1 - s) (beta k)) with hP
  have hPpos : ∀ k, 0 < P k := fun k => by
    have := X7A14_phiPlus_pos (p := s) (ha k)
    have := X7A14_phiMinus_pos hs0 (ha k)
    have := X7A14_phiPlus_pos (p := 1 - s) (hb k)
    have := X7A14_phiMinus_pos hs1' (hb k)
    simp only [hP]; positivity
  set a : ℝ := ∏ k, spectralPsi n s (alpha k) (beta k) with ha_def
  set b : ℝ := ∏ k, spectralPsi n (1 - s) (beta k) (alpha k) with hb_def
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpsi1 : ∀ k, 0 < phiPlus s (alpha k) * phiMinus (1 - s) (beta k) := fun k => by
    have := X7A14_phiPlus_pos (p := s) (ha k)
    have := X7A14_phiMinus_pos hs1' (hb k)
    positivity
  have hpsi2 : ∀ k, 0 < phiPlus (1 - s) (beta k) * phiMinus s (alpha k) := fun k => by
    have := X7A14_phiPlus_pos (p := 1 - s) (hb k)
    have := X7A14_phiMinus_pos hs0 (ha k)
    positivity
  have hapos : 0 < a := by
    simp only [ha_def, spectralPsi]
    exact Finset.prod_pos fun k _ => Real.rpow_pos_of_pos (hpsi1 k) _
  have hbpos : 0 < b := by
    simp only [hb_def, spectralPsi, sub_sub_cancel]
    exact Finset.prod_pos fun k _ => Real.rpow_pos_of_pos (hpsi2 k) _
  have hab : a * b = ∏ k, P k ^ (1 / (n : ℝ)) := by
    simp only [ha_def, hb_def, spectralPsi, sub_sub_cancel, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [Real.rpow_eq_pow]
    rw [← Real.mul_rpow (hpsi1 k).le (hpsi2 k).le]
    congr 1; simp only [hP]; ring
  have habn : (a * b) ^ n = ∏ k, P k := by
    rw [hab, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hPpos k).le]
    field_simp; simp
  set c : ℝ := Real.sqrt (a * b) with hc
  have hcpos : 0 < c := Real.sqrt_pos.mpr (mul_pos hapos hbpos)
  have hc2 : c ^ 2 = a * b := Real.sq_sqrt (mul_pos hapos hbpos).le
  have hprodsqrt : ∏ k, Real.sqrt (P k) = c ^ n := by
    have h1 : 0 ≤ ∏ k, Real.sqrt (P k) := Finset.prod_nonneg fun k _ => Real.sqrt_nonneg _
    rw [← pow_left_inj₀ h1 (pow_nonneg hcpos.le n) two_ne_zero, ← Finset.prod_pow]
    rw [← pow_mul, mul_comm, pow_mul, hc2, habn]
    exact Finset.prod_congr rfl fun k _ => Real.sq_sqrt (hPpos k).le
  have hY : youngFunction alpha beta s = 2 ^ n / c ^ n := by
    unfold youngFunction spectralGamma
    rw [← hprodsqrt, div_eq_mul_inv, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [X7A14_D (ha k), X7A14_D (hb k), ← mul_inv, ← Real.sqrt_mul]
    · have := X7A14_phiPlus_pos (p := s) (ha k)
      have := X7A14_phiMinus_pos hs0 (ha k)
      positivity
  have hM : minkowskiFunction alpha beta s = 4 ^ n / (a + b) ^ n := rfl
  rw [hM, hY]
  have hamgm : 2 * c ≤ a + b := by
    have h : (2 * c) ^ 2 ≤ (a + b) ^ 2 := by nlinarith [sq_nonneg (a - b)]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h
  calc (4 : ℝ) ^ n / (a + b) ^ n ≤ 4 ^ n / (2 * c) ^ n := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact pow_le_pow_left₀ (by positivity) hamgm n
    _ = 2 ^ n / c ^ n := by
        rw [mul_pow, show (4 : ℝ) ^ n = 2 ^ n * 2 ^ n by rw [← mul_pow]; norm_num]
        field_simp

lemma X7A14_bound {n : ℕ} (hn : 0 < n) (alpha beta : Fin n → ℝ)
    (ha : ∀ k, 1 ≤ alpha k) (hb : ∀ k, 1 ≤ beta k) (N : ℕ) :
    minkowskiBound alpha beta N ≤ youngBound alpha beta N := by
  unfold minkowskiBound youngBound halfInfPower
  gcongr with s
  exact (X7A14_pointwise hn alpha beta ha hb s.2.1 s.2.2)

end QAlgorithms.Papers.Independent.Claimed50.P30

end

open scoped BigOperators ENNReal NNReal ComplexOrder Topology

open Filter MeasureTheory

noncomputable section

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

open QAlgorithms.Papers.Independent.Claimed50.P30 in
theorem solution {n : ℕ} (hn : 0 < n) (W : FockWeylSystem n)
    (A B : GaussianState n W) (DA : NormalModes A) (DB : NormalModes B)
    (N : ℕ) (hN : 0 < N) :
    minkowskiBound DA.spectrum DB.spectrum N ≤ youngBound DA.spectrum DB.spectrum N :=
  X7A14_bound hn _ _ DA.spectrum_ge_one DB.spectrum_ge_one N

end
