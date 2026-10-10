-- Prove2me | solution 1 for QInfo.exists_rangeProjector_mul_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-09T14:44:48.878219+00:00
-- url     : https://prove2.me/submissions/3e380e8b-25fd-4fc1-90d5-15db298d4be4

import Mathlib
open Matrix
open scoped ComplexOrder

theorem solution {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (W : Matrix m n ℂ) :
    ∃ Gp : Matrix m m ℂ, Gp.IsHermitian ∧ (W * Wᴴ) * Gp = Gp * (W * Wᴴ) ∧
      (W * Wᴴ) * Gp * W = W := by
  have hG : (W * Wᴴ).IsHermitian := isHermitian_mul_conjTranspose_self W
  obtain ⟨G, hGdef⟩ : ∃ G, G = W * Wᴴ := ⟨_, rfl⟩
  rw [← hGdef] at hG ⊢
  let U : Matrix m m ℂ := (hG.eigenvectorUnitary : Matrix m m ℂ)
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  let D : Matrix m m ℂ := diagonal (fun i => (hG.eigenvalues i : ℂ))
  let Dp : Matrix m m ℂ := diagonal (fun i => ((hG.eigenvalues i : ℂ))⁻¹)
  have hspec : G = U * D * star U := hG.spectral_theorem
  have hDDp : D * Dp = Dp * D := by
    simp only [D, Dp, diagonal_mul_diagonal]; congr 1; ext i; ring
  have hDDpD : D * Dp * D = D := by
    simp only [D, Dp, diagonal_mul_diagonal]; congr 1; ext i
    by_cases h : (hG.eigenvalues i : ℂ) = 0
    · simp [h]
    · rw [mul_inv_cancel₀ h, one_mul]
  have hGGp : G * (U * Dp * star U) = (U * Dp * star U) * G := by
    rw [hspec]
    calc U * D * star U * (U * Dp * star U) = U * (D * (star U * U) * Dp) * star U := by
            simp only [Matrix.mul_assoc]
      _ = U * (Dp * (star U * U) * D) * star U := by rw [hUU, Matrix.mul_one, Matrix.mul_one, hDDp]
      _ = U * Dp * star U * (U * D * star U) := by simp only [Matrix.mul_assoc]
  have hGGpG : G * (U * Dp * star U) * G = G := by
    rw [hspec]
    calc U * D * star U * (U * Dp * star U) * (U * D * star U)
          = U * (D * (star U * U) * Dp * (star U * U) * D) * star U := by
            simp only [Matrix.mul_assoc]
      _ = U * D * star U := by
            rw [hUU, Matrix.mul_one, Matrix.mul_one, hDDpD, Matrix.mul_assoc]
  have hGpH : (U * Dp * star U).IsHermitian := by
    have hDp : Dpᴴ = Dp := by
      simp only [Dp, diagonal_conjTranspose]; congr 1; ext i; simp
    show (U * Dp * star U)ᴴ = U * Dp * star U
    rw [conjTranspose_mul, conjTranspose_mul, hDp, star_eq_conjTranspose,
      conjTranspose_conjTranspose, Matrix.mul_assoc]
  generalize U * Dp * star U = Gp at hGGp hGGpG hGpH
  refine ⟨Gp, hGpH, hGGp, ?_⟩
  -- `P = G Gp` is a Hermitian idempotent with `P G = G = G P`, hence `(1 - P) W = 0`.
  have hPH : (G * Gp)ᴴ = G * Gp := by
    rw [conjTranspose_mul, hGpH.eq, hG.eq, hGGp]
  have hGP : G * (G * Gp) = G := by
    rw [hGGp, ← Matrix.mul_assoc, hGGpG]
  have h0 : ((1 - G * Gp) * W) * ((1 - G * Gp) * W)ᴴ = 0 := by
    rw [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hPH]
    calc (1 - G * Gp) * W * (Wᴴ * (1 - G * Gp)) = (1 - G * Gp) * G * (1 - G * Gp) := by
          rw [hGdef]; simp only [Matrix.mul_assoc]
      _ = 0 := by
          rw [Matrix.sub_mul, Matrix.one_mul, hGGpG, sub_self, Matrix.zero_mul]
  have h1 : (1 - G * Gp) * W = 0 := self_mul_conjTranspose_eq_zero.mp h0
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
  exact h1.symm

