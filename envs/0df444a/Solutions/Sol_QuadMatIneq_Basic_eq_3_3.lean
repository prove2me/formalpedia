-- Prove2me | solution 1 for QuadMatIneq.Basic.eq_3_3
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T18:03:01.038222+00:00
-- url     : https://prove2.me/submissions/5cd0b043-98d6-4c7a-938e-f2886ba160a3

import Definitions.Def_QuadMatIneq_Basic_QMI

open Matrix QuadMatIneq.Basic
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


private lemma penrose_unique {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α β ℝ) (X Y : Matrix β α ℝ)
    (hX : IsMoorePenrose A X) (hY : IsMoorePenrose A Y) : X = Y := by
  have hAX : A * X = A * Y := by
    have e : (A * X) * (A * Y) = A * Y := by
      rw [← Matrix.mul_assoc, hX.1]
    have f : (A * Y) * (A * X) = A * X := by
      rw [← Matrix.mul_assoc, hY.1]
    have t := congrArg Matrix.transpose f
    rw [transpose_mul, hX.2.2.1, hY.2.2.1] at t
    exact t.symm.trans e
  have hXA : X * A = Y * A := by
    have e : (X * A) * (Y * A) = X * A := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc A, hY.1]
    have f : (Y * A) * (X * A) = Y * A := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc A, hX.1]
    have t := congrArg Matrix.transpose f
    rw [transpose_mul, hX.2.2.2, hY.2.2.2] at t
    exact e.symm.trans t
  calc
    X = X * A * X := hX.2.1.symm
    _ = Y * A * X := by rw [hXA]
    _ = Y * (A * Y) := by rw [Matrix.mul_assoc, hAX]
    _ = Y := by rw [← Matrix.mul_assoc, hY.2.1]
private lemma pinv_symm {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) (hA : Aᵀ = A) : (pinv A)ᵀ = pinv A := by
  have h := pinv_penrose A
  have ht : IsMoorePenrose A (pinv A)ᵀ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have e := congrArg Matrix.transpose h.1
      simpa only [transpose_mul, hA, Matrix.mul_assoc] using e
    · have e := congrArg Matrix.transpose h.2.1
      simpa only [transpose_mul, hA, Matrix.mul_assoc] using e
    · have e := h.2.2.2
      simpa only [transpose_mul, transpose_transpose, hA] using e.symm
    · have e := h.2.2.1
      simpa only [transpose_mul, transpose_transpose, hA] using e.symm
  exact penrose_unique A _ _ ht h
private lemma form_expand {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (Z : Matrix κ ι ℝ) :
    qmiForm P Z = P.toBlocks₁₁ + P.toBlocks₁₂ * Z + Zᵀ * P.toBlocks₂₁ +
      Zᵀ * P.toBlocks₂₂ * Z := by
  rw [qmiForm, ← Matrix.fromBlocks_toBlocks P, transpose_fromRows,
    fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  simp only [transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.add_mul, Matrix.mul_add, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂,
    toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
  abel

theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : P.IsHermitian) (h22 : (-P.toBlocks₂₂).PosSemidef)
    (hker : ∀ v : κ → ℝ, P.toBlocks₂₂ *ᵥ v = 0 → P.toBlocks₁₂ *ᵥ v = 0)
    (Z : Matrix κ ι ℝ) :
    qmiForm P Z = schur P +
      (Z + pinv P.toBlocks₂₂ * P.toBlocks₂₁)ᵀ * P.toBlocks₂₂ *
        (Z + pinv P.toBlocks₂₂ * P.toBlocks₂₁) := by
  have hPt : Pᵀ = P := by simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hP
  have hDt : P.toBlocks₂₂ᵀ = P.toBlocks₂₂ := by
    exact congrArg Matrix.toBlocks₂₂ hPt
  have hCt : P.toBlocks₂₁ᵀ = P.toBlocks₁₂ := by
    exact congrArg Matrix.toBlocks₁₂ hPt
  have hBt : P.toBlocks₁₂ᵀ = P.toBlocks₂₁ := by
    exact congrArg Matrix.toBlocks₂₁ hPt
  have hX := pinv_penrose P.toBlocks₂₂
  have hXt := pinv_symm P.toBlocks₂₂ hDt
  have hproj : P.toBlocks₁₂ * (1 - pinv P.toBlocks₂₂ * P.toBlocks₂₂) = 0 := by
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
    apply hker
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
      hX.1, sub_self, Matrix.zero_mulVec]
  have hB : P.toBlocks₁₂ * pinv P.toBlocks₂₂ * P.toBlocks₂₂ = P.toBlocks₁₂ := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, sub_eq_zero] at hproj
    exact hproj.symm
  have hC : P.toBlocks₂₂ * pinv P.toBlocks₂₂ * P.toBlocks₂₁ = P.toBlocks₂₁ := by
    have e := congrArg Matrix.transpose hB
    simpa only [transpose_mul, hDt, hXt, hBt, Matrix.mul_assoc] using e
  rw [form_expand, schur, transpose_add, transpose_mul, hCt, hXt]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
  have hBZ : P.toBlocks₁₂ * (pinv P.toBlocks₂₂ * (P.toBlocks₂₂ * Z)) = P.toBlocks₁₂ * Z := by
    simpa only [Matrix.mul_assoc] using congrArg (fun T => T * Z) hB
  have hC' : P.toBlocks₂₂ * (pinv P.toBlocks₂₂ * P.toBlocks₂₁) = P.toBlocks₂₁ := by
    simpa only [Matrix.mul_assoc] using hC
  rw [hBZ, hC']
  abel
