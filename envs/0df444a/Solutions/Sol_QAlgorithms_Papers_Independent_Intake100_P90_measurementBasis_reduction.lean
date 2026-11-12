-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P90.measurementBasis_reduction
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T01:50:11.947072+00:00
-- url     : https://prove2.me/submissions/c70e5b38-a28f-42e1-bf43-168b27278222

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P90

noncomputable section

open scoped ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace Aux_measurementBasis

open QAlgorithms

theorem pd_mul_diag {I : Type*} [Fintype I] [DecidableEq I] (x : I) (d : I → ℂ) :
    pureDensity (ket x) * Matrix.diagonal d = d x • pureDensity (ket x) := by
  ext a b
  simp only [Matrix.mul_diagonal, Matrix.smul_apply, pureDensity, Matrix.of_apply, ket,
    EuclideanSpace.single_apply, smul_eq_mul]
  by_cases hb : b = x
  · rw [hb, if_pos rfl, map_one]
    ring
  · rw [if_neg hb, map_zero]
    ring

theorem diag_mul_pd {I : Type*} [Fintype I] [DecidableEq I] (x : I) (d : I → ℂ) :
    Matrix.diagonal d * pureDensity (ket x) = d x • pureDensity (ket x) := by
  ext a b
  simp only [Matrix.diagonal_mul, Matrix.smul_apply, pureDensity, Matrix.of_apply, ket,
    EuclideanSpace.single_apply, smul_eq_mul]
  by_cases ha : a = x
  · rw [ha]
  · rw [if_neg ha]
    ring

theorem unit_norm (z : ℂ) (h : Complex.normSq z = 1) : z * star z = 1 := by
  rw [show star z = conj z from rfl, Complex.mul_conj, h, Complex.ofReal_one]

end Aux_measurementBasis

open QAlgorithms QAlgorithms.Papers.Independent.Intake100.P90 Aux_measurementBasis in
theorem solution {I J K : Type*}
    [Fintype I] [Fintype J] [Fintype K] [DecidableEq I] [DecidableEq J]
    (rho : Matrix (I × J) (I × J) ℂ) (hrho : IsDensityMatrix rho)
    (p : K → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : ∑ k, p k = 1)
    (OA : K → Matrix.unitaryGroup I ℂ) (OB : K → Matrix.unitaryGroup J ℂ)
    (hA : ∀ k, ∃ d : I → ℂ, (∀ x, Complex.normSq (d x) = 1) ∧
      (OA k : Matrix I I ℂ) = Matrix.diagonal d)
    (hBB : ∀ k, ∃ d : J → ℂ, (∀ x, Complex.normSq (d x) = 1) ∧
      (OB k : Matrix J J ℂ) = Matrix.diagonal d) :
    (∀ x : I, let P := Matrix.kronecker (pureDensity (ket x)) (1 : Matrix J J ℂ)
      P * mixOnFirst p (fun k => (OA k : Matrix I I ℂ)) rho * P = P * rho * P) ∧
    (∀ y : J, let P := Matrix.kronecker (1 : Matrix I I ℂ) (pureDensity (ket y))
      P * mixOnSecond p (fun k => (OB k : Matrix J J ℂ)) rho * P = P * rho * P) := by
  have hsumC : (∑ k, (p k : ℂ)) = 1 := by
    rw [← Complex.ofReal_sum, hsum, Complex.ofReal_one]
  constructor
  · intro x P
    have key : ∀ k, P * ((p k : ℂ) • (Matrix.kronecker (OA k : Matrix I I ℂ) (1 : Matrix J J ℂ) *
        rho * (Matrix.kronecker (OA k : Matrix I I ℂ) (1 : Matrix J J ℂ)).conjTranspose)) * P =
        (p k : ℂ) • (P * rho * P) := by
      intro k
      obtain ⟨d, hd, hOd⟩ := hA k
      rw [hOd, Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      have h1 : P * Matrix.kronecker (Matrix.diagonal d) (1 : Matrix J J ℂ) = d x • P := by
        show Matrix.kroneckerMap (· * ·) (pureDensity (ket x)) (1 : Matrix J J ℂ) *
          Matrix.kroneckerMap (· * ·) (Matrix.diagonal d) (1 : Matrix J J ℂ) = _
        rw [← Matrix.mul_kronecker_mul, pd_mul_diag, Matrix.mul_one, Matrix.smul_kronecker]
        try rfl
      have h2 : (Matrix.kronecker (Matrix.diagonal d) (1 : Matrix J J ℂ)).conjTranspose * P =
          star (d x) • P := by
        show (Matrix.kroneckerMap (· * ·) (Matrix.diagonal d) (1 : Matrix J J ℂ)).conjTranspose *
          Matrix.kroneckerMap (· * ·) (pureDensity (ket x)) (1 : Matrix J J ℂ) = _
        rw [Matrix.conjTranspose_kronecker, Matrix.diagonal_conjTranspose, Matrix.conjTranspose_one,
          ← Matrix.mul_kronecker_mul, diag_mul_pd, Matrix.mul_one, Matrix.smul_kronecker]
        try rfl
      calc P * (Matrix.kronecker (Matrix.diagonal d) (1 : Matrix J J ℂ) * rho *
            (Matrix.kronecker (Matrix.diagonal d) (1 : Matrix J J ℂ)).conjTranspose) * P
          = (P * Matrix.kronecker (Matrix.diagonal d) (1 : Matrix J J ℂ)) * rho *
            ((Matrix.kronecker (Matrix.diagonal d) (1 : Matrix J J ℂ)).conjTranspose * P) := by
            simp only [Matrix.mul_assoc]
        _ = (d x • P) * rho * (star (d x) • P) := by rw [h1, h2]
        _ = (star (d x) * d x) • (P * rho * P) := by
            simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        _ = P * rho * P := by rw [mul_comm (star (d x)), unit_norm _ (hd x), one_smul]
    calc P * mixOnFirst p (fun k => (OA k : Matrix I I ℂ)) rho * P
        = ∑ k, P * ((p k : ℂ) • (Matrix.kronecker (OA k : Matrix I I ℂ) (1 : Matrix J J ℂ) *
          rho * (Matrix.kronecker (OA k : Matrix I I ℂ) (1 : Matrix J J ℂ)).conjTranspose)) * P := by
          unfold mixOnFirst
          rw [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ k, (p k : ℂ) • (P * rho * P) := Finset.sum_congr rfl (fun k _ => key k)
      _ = (∑ k, (p k : ℂ)) • (P * rho * P) := Finset.sum_smul.symm
      _ = P * rho * P := by rw [hsumC, one_smul]
  · intro y P
    have key : ∀ k, P * ((p k : ℂ) • (Matrix.kronecker (1 : Matrix I I ℂ) (OB k : Matrix J J ℂ) *
        rho * (Matrix.kronecker (1 : Matrix I I ℂ) (OB k : Matrix J J ℂ)).conjTranspose)) * P =
        (p k : ℂ) • (P * rho * P) := by
      intro k
      obtain ⟨d, hd, hOd⟩ := hBB k
      rw [hOd, Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      have h1 : P * Matrix.kronecker (1 : Matrix I I ℂ) (Matrix.diagonal d) = d y • P := by
        show Matrix.kroneckerMap (· * ·) (1 : Matrix I I ℂ) (pureDensity (ket y)) *
          Matrix.kroneckerMap (· * ·) (1 : Matrix I I ℂ) (Matrix.diagonal d) = _
        rw [← Matrix.mul_kronecker_mul, pd_mul_diag, Matrix.mul_one, Matrix.kronecker_smul]
        try rfl
      have h2 : (Matrix.kronecker (1 : Matrix I I ℂ) (Matrix.diagonal d)).conjTranspose * P =
          star (d y) • P := by
        show (Matrix.kroneckerMap (· * ·) (1 : Matrix I I ℂ) (Matrix.diagonal d)).conjTranspose *
          Matrix.kroneckerMap (· * ·) (1 : Matrix I I ℂ) (pureDensity (ket y)) = _
        rw [Matrix.conjTranspose_kronecker, Matrix.diagonal_conjTranspose, Matrix.conjTranspose_one,
          ← Matrix.mul_kronecker_mul, diag_mul_pd, Matrix.mul_one, Matrix.kronecker_smul]
        try rfl
      calc P * (Matrix.kronecker (1 : Matrix I I ℂ) (Matrix.diagonal d) * rho *
            (Matrix.kronecker (1 : Matrix I I ℂ) (Matrix.diagonal d)).conjTranspose) * P
          = (P * Matrix.kronecker (1 : Matrix I I ℂ) (Matrix.diagonal d)) * rho *
            ((Matrix.kronecker (1 : Matrix I I ℂ) (Matrix.diagonal d)).conjTranspose * P) := by
            simp only [Matrix.mul_assoc]
        _ = (d y • P) * rho * (star (d y) • P) := by rw [h1, h2]
        _ = (star (d y) * d y) • (P * rho * P) := by
            simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        _ = P * rho * P := by rw [mul_comm (star (d y)), unit_norm _ (hd y), one_smul]
    calc P * mixOnSecond p (fun k => (OB k : Matrix J J ℂ)) rho * P
        = ∑ k, P * ((p k : ℂ) • (Matrix.kronecker (1 : Matrix I I ℂ) (OB k : Matrix J J ℂ) *
          rho * (Matrix.kronecker (1 : Matrix I I ℂ) (OB k : Matrix J J ℂ)).conjTranspose)) * P := by
          unfold mixOnSecond
          rw [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ k, (p k : ℂ) • (P * rho * P) := Finset.sum_congr rfl (fun k _ => key k)
      _ = (∑ k, (p k : ℂ)) • (P * rho * P) := Finset.sum_smul.symm
      _ = P * rho * P := by rw [hsumC, one_smul]

end
