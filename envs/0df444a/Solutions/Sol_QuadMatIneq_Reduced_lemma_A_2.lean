-- Prove2me | solution 1 for QuadMatIneq.Reduced.lemma_A_2
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T18:01:25.465446+00:00
-- url     : https://prove2.me/submissions/e3789175-2861-4a87-9ebb-6b1f30107fc2

import Definitions.Def_QuadMatIneq_Reduced_QMI

open Matrix QuadMatIneq.Reduced
open scoped MatrixOrder
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section

private lemma hermitian_generalized_inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.IsHermitian) :
    ∃ C : Matrix ι ι ℝ, Cᵀ = C ∧ G * C = C * G ∧ G * C * G = G ∧ C * G * C = C := by
  let φ := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) hG.eigenvectorUnitary
  let d := hG.eigenvalues
  have hspec : G = φ (diagonal d) := by
    simpa [φ, d] using hG.spectral_theorem
  have hde : diagonal d * diagonal (fun i => (d i)⁻¹) =
      diagonal (fun i => (d i)⁻¹) * diagonal d := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hded : diagonal d * diagonal (fun i => (d i)⁻¹) * diagonal d = diagonal d := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : d i = 0 <;> simp [hi]
  have hede : diagonal (fun i => (d i)⁻¹) * diagonal d *
      diagonal (fun i => (d i)⁻¹) = diagonal (fun i => (d i)⁻¹) := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : d i = 0 <;> simp [hi]
  refine ⟨φ (diagonal (fun i => (d i)⁻¹)), ?_, ?_, ?_, ?_⟩
  · have hh : (φ (diagonal (fun i => (d i)⁻¹))).IsHermitian := by
      change star (φ (diagonal (fun i => (d i)⁻¹))) = _
      rw [← map_star]
      congr 1
      exact isHermitian_diagonal_of_self_adjoint _ (by rfl)
    simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hh
  · rw [hspec, ← map_mul, ← map_mul, hde]
  · rw [hspec, ← map_mul, ← map_mul, hded]
  · rw [hspec, ← map_mul, ← map_mul, hede]

private lemma exists_moore_penrose {ι σ : Type*} [Fintype ι] [Fintype σ]
    [DecidableEq ι] [DecidableEq σ] (B : Matrix σ ι ℝ) :
    ∃ X : Matrix ι σ ℝ, IsMoorePenrose B X := by
  obtain ⟨C, hCt, hcomm, hgcg, hcgc⟩ :=
    hermitian_generalized_inverse (Bᵀ * B) (by
      simpa only [conjTranspose_eq_transpose_of_trivial] using isHermitian_conjTranspose_mul_self B)
  have hbcg : B * C * (Bᵀ * B) = B := by
    have hgzero : (Bᵀ * B) * (C * (Bᵀ * B) - 1) = 0 := by
      rw [mul_sub, ← mul_assoc, hgcg, Matrix.mul_one, sub_self]
    have hbzero : B * (C * (Bᵀ * B) - 1) = 0 := by
      exact (conjTranspose_mul_self_mul_eq_zero B _).mp
        (by simpa only [conjTranspose_eq_transpose_of_trivial] using hgzero)
    have := hbzero
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, sub_eq_zero] at this
    exact this
  refine ⟨C * Bᵀ, ?_, ?_, ?_, ?_⟩
  · simpa only [IsMoorePenrose, Matrix.mul_assoc] using hbcg
  · calc
      C * Bᵀ * B * (C * Bᵀ) = (C * (Bᵀ * B) * C) * Bᵀ := by simp only [Matrix.mul_assoc]
      _ = C * Bᵀ := by rw [hcgc]
  · simp only [transpose_mul, transpose_transpose, hCt]
    simp only [Matrix.mul_assoc]
  · simp only [transpose_mul, transpose_transpose, hCt]
    simpa only [Matrix.mul_assoc] using hcomm

private lemma pinv_penrose {ι σ : Type*} [Fintype ι] [Fintype σ]
    [DecidableEq ι] [DecidableEq σ] (B : Matrix σ ι ℝ) :
    IsMoorePenrose B (pinv B) := by
  exact Classical.epsilon_spec (exists_moore_penrose B)

theorem solution {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β]
    (A : Matrix α β ℝ) (B : Matrix α γ ℝ) (M : Matrix β γ ℝ) :
    A * M = B ↔
      LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin ∧
        ∃ T : Matrix β γ ℝ, M = pinv A * B + (1 - pinv A * A) * T := by
  classical
  have hP := pinv_penrose A
  constructor
  · intro h
    constructor
    · rw [← h, Matrix.mulVecLin_mul]
      exact LinearMap.range_comp_le_range _ _
    · refine ⟨M, ?_⟩
      rw [← h, Matrix.sub_mul, Matrix.one_mul]
      simp only [Matrix.mul_assoc]
      abel
  · rintro ⟨hr, T, hT⟩
    have hAB : A * pinv A * B = B := by
      apply Matrix.ext_iff_mulVec.mpr
      intro v
      obtain ⟨w, hw⟩ := hr (show B.mulVecLin v ∈ LinearMap.range B.mulVecLin from ⟨v, rfl⟩)
      rw [← Matrix.mulVec_mulVec]
      change A *ᵥ w = B *ᵥ v at hw
      rw [← hw, Matrix.mulVec_mulVec, hP.1]
    rw [hT, Matrix.mul_add, ← Matrix.mul_assoc, hAB]
    have hz : A * (1 - pinv A * A) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hP.1, sub_self]
    rw [← Matrix.mul_assoc, hz, Matrix.zero_mul, add_zero]
