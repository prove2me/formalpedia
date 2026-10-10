-- Prove2me | solution 1 for QInfo.commute_mul_conjTranspose_iff_exists_mirror
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-09T14:44:49.871585+00:00
-- url     : https://prove2.me/submissions/d75908ae-8c0b-4957-a364-1efbec07b250

import Mathlib
import Theorems.Thm_QInfo_exists_rangeProjector_mul_conjTranspose
open Matrix
open scoped ComplexOrder

theorem solution {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (W : Matrix m n ℂ) (A : Matrix m m ℂ) :
    A * (W * Wᴴ) = (W * Wᴴ) * A ↔ ∃ B : Matrix n n ℂ, A * W = W * B ∧ Aᴴ * W = W * Bᴴ := by
  constructor
  · intro hA
    obtain ⟨Gp, hGp, hc, hW⟩ := QInfo.exists_rangeProjector_mul_conjTranspose W
    have hGH' : (W * Wᴴ)ᴴ = W * Wᴴ := (isHermitian_mul_conjTranspose_self W).eq
    obtain ⟨G, hGdef⟩ : ∃ G, G = W * Wᴴ := ⟨_, rfl⟩
    rw [← hGdef] at hA hc hW hGH'
    have hGH : Gᴴ = G := hGH'
    have hAH : Aᴴ * G = G * Aᴴ := by
      have := congrArg conjTranspose hA
      rw [conjTranspose_mul, conjTranspose_mul, hGH] at this
      exact this.symm
    have hGGpG : G * Gp * G = G := by
      calc G * Gp * G = (G * Gp * W) * Wᴴ := by
            conv_lhs => rw [hGdef]
            conv_rhs => rw [hGdef]
            simp only [Matrix.mul_assoc]
        _ = G := by rw [hW, hGdef]
    have e1 : A * W = G * (A * (Gp * W)) := by
      calc A * W = A * (G * Gp * W) := by rw [hW]
        _ = (A * G) * (Gp * W) := by simp only [Matrix.mul_assoc]
        _ = G * (A * (Gp * W)) := by rw [hA]; simp only [Matrix.mul_assoc]
    refine ⟨Wᴴ * Gp * A * W, ?_, ?_⟩
    · calc A * W = G * (A * (Gp * W)) := e1
        _ = (G * Gp * G) * (A * (Gp * W)) := by rw [hGGpG]
        _ = G * Gp * (G * (A * (Gp * W))) := by simp only [Matrix.mul_assoc]
        _ = G * Gp * (A * W) := by rw [← e1]
        _ = W * (Wᴴ * Gp * A * W) := by rw [hGdef]; simp only [Matrix.mul_assoc]
    · calc Aᴴ * W = Aᴴ * (G * Gp * W) := by rw [hW]
        _ = (Aᴴ * G) * (Gp * W) := by simp only [Matrix.mul_assoc]
        _ = W * (Wᴴ * Gp * A * W)ᴴ := by
          rw [hAH, conjTranspose_mul, conjTranspose_mul, conjTranspose_mul,
            conjTranspose_conjTranspose, hGp.eq]
          rw [hGdef]; simp only [Matrix.mul_assoc]
  · rintro ⟨B, h1, h2⟩
    calc A * (W * Wᴴ) = (A * W) * Wᴴ := (Matrix.mul_assoc _ _ _).symm
      _ = W * (B * Wᴴ) := by rw [h1, Matrix.mul_assoc]
      _ = W * (Aᴴ * W)ᴴ := by rw [h2, conjTranspose_mul, conjTranspose_conjTranspose]
      _ = W * Wᴴ * A := by rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

