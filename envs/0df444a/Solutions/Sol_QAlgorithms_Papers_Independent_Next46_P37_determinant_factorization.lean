-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P37.determinant_factorization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T16:37:14.299991+00:00
-- url     : https://prove2.me/submissions/92c4df2c-2a0a-4118-8ab9-3cc74a0957de

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P37
noncomputable section

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)
open QAlgorithms.Papers.Independent.Next46.P37
open Matrix

theorem g62p_detK (n : ℕ) :
    (fromBlocks (0 : Matrix (Fin n) (Fin n) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) (0 : Matrix (Fin n) (Fin n) ℝ)).det = (-1) ^ n := by
  have h : fromBlocks (0 : Matrix (Fin n) (Fin n) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) (0 : Matrix (Fin n) (Fin n) ℝ) =
      fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ) (0 : Matrix (Fin n) (Fin n) ℝ) (-1 : Matrix (Fin n) (Fin n) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) * fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) (0 : Matrix (Fin n) (Fin n) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) *
        fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ) (0 : Matrix (Fin n) (Fin n) ℝ) (-1 : Matrix (Fin n) (Fin n) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) *
        fromBlocks (-1 : Matrix (Fin n) (Fin n) ℝ) (0 : Matrix (Fin n) (Fin n) ℝ) (0 : Matrix (Fin n) (Fin n) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) := by
    simp only [fromBlocks_multiply]
    congr 1 <;> simp
  rw [h]
  simp only [det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁]
  simp [det_neg]

theorem g62p_symp {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) ℝ)
    (hS : fromBlocks A B C D ∈ symplecticGroup (Fin n) ℝ) (hB : B.det ≠ 0) :
    D * B⁻¹ * A - C = (Bᵀ)⁻¹ := by
  rw [SymplecticGroup.mem_iff'] at hS
  simp only [fromBlocks_transpose, J, fromBlocks_multiply] at hS
  simp only [mul_zero, zero_add, add_zero, mul_neg, mul_one, neg_mul, one_mul] at hS
  obtain ⟨-, -, h21, h22⟩ := fromBlocks_inj.1 hS
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.2 hB
  have key : Bᵀ * (D * B⁻¹ * A - C) = 1 := by
    have e : Bᵀ * D = Dᵀ * B := by
      have : Dᵀ * B + -(Bᵀ * D) = 0 := h22
      rw [add_neg_eq_zero] at this; exact this.symm
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e, Matrix.mul_assoc Dᵀ B,
      mul_nonsing_inv _ hBu, Matrix.mul_one]
    have : Dᵀ * A + -(Bᵀ * C) = 1 := h21
    rw [← this, sub_eq_add_neg]
  exact (Matrix.inv_eq_right_inv key).symm

theorem solution (n : ℕ) (hn : 0 < n)
    (A B C D : Matrix (Fin n) (Fin n) ℝ)
    (hS : Matrix.fromBlocks A B C D ∈ Matrix.symplecticGroup (Fin n) ℝ)
    (hB : B.det ≠ 0) :
    let S := Matrix.fromBlocks A B C D
    let P := D * B⁻¹
    let L := B⁻¹
    let Q := B⁻¹ * A
    (S - 1).det = (-1 : ℝ) ^ n * B.det *
      (B⁻¹ * A + D * B⁻¹ - B⁻¹ - (B.transpose)⁻¹).det ∧
    (S - 1).det = (-1 : ℝ) ^ n * (L⁻¹).det * (diagonalHessian P L Q).det := by
  intro S P L Q
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.2 hB
  have hsym := g62p_symp A B C D hS hB
  set X := B⁻¹ * A + D * B⁻¹ - B⁻¹ - (B.transpose)⁻¹ with hX
  have hfac : S - 1 = fromBlocks 1 0 ((D - 1) * B⁻¹) 1 * fromBlocks B (A - 1) 0 X *
      fromBlocks (0 : Matrix (Fin n) (Fin n) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) 1 0 := by
    have h1 : (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) = fromBlocks 1 0 0 1 :=
      fromBlocks_one.symm
    have hsub : S - fromBlocks 1 0 0 1 = fromBlocks (A - 1) B C (D - 1) := by
      ext i j <;> rcases i with i | i <;> rcases j with j | j <;> simp [S, Matrix.one_apply]
    rw [h1, hsub]
    simp only [fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.zero_mul, Matrix.one_mul, zero_add, add_zero]
    congr 1
    swap
    · rw [Matrix.mul_assoc, nonsing_inv_mul _ hBu, Matrix.mul_one]
    · have : C = D * B⁻¹ * A - (Bᵀ)⁻¹ := by rw [← hsym]; abel
      rw [this, hX]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
      abel
  have hdet : (S - 1).det = (-1 : ℝ) ^ n * B.det * X.det := by
    rw [hfac, det_mul, det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁, g62p_detK]
    simp; ring
  refine ⟨hdet, ?_⟩
  rw [hdet]
  have hL : L⁻¹ = B := nonsing_inv_nonsing_inv B hBu
  have hH : diagonalHessian P L Q = X := by
    simp only [diagonalHessian, P, L, Q, hX, transpose_nonsing_inv]
    abel
  rw [hL, hH]
