-- Prove2me | solution 1 for QuadMatIneq.Reduced.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T16:27:53.888116+00:00
-- url     : https://prove2.me/submissions/cbd20f10-32ea-43f0-9724-64b1ff62eb9f

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

private lemma gram_dom_kernel {ι ρ σ τ : Type*} [Fintype ι] [Fintype ρ]
    [Fintype σ] [Fintype τ] [DecidableEq τ]
    (A : Matrix ρ ι ℝ) (B : Matrix σ ι ℝ) (Z : Matrix ι τ ℝ)
    (hdom : (Bᵀ * B - Aᵀ * A).PosSemidef) (hBZ : B * Z = 0) : A * Z = 0 := by
  have hcong := hdom.conjTranspose_mul_mul_same Z
  have heq : Zᵀ * (Bᵀ * B - Aᵀ * A) * Z = -((A * Z)ᵀ * (A * Z)) := by
    calc
      _ = (B * Z)ᵀ * (B * Z) - (A * Z)ᵀ * (A * Z) := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hBZ]; simp
  have hneg : (-((A * Z)ᵀ * (A * Z))).PosSemidef := by
    rw [← heq]
    simpa only [conjTranspose_eq_transpose_of_trivial] using hcong
  have hgram : ((A * Z)ᵀ * (A * Z)).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      posSemidef_conjTranspose_mul_self (A * Z)
  have hle : (A * Z)ᵀ * (A * Z) ≤ 0 := by
    simpa only [Matrix.le_iff, zero_sub] using hneg
  have hz := le_antisymm hle hgram.nonneg
  exact (conjTranspose_mul_self_eq_zero).mp
    (by simpa only [conjTranspose_eq_transpose_of_trivial] using hz)

private lemma projection_complement {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : Matrix σ σ ℝ) (ht : Pᵀ = P) (hi : P * P = P) : (1 - P).PosSemidef := by
  have heq : (1 - P)ᵀ * (1 - P) = 1 - P := by
    rw [transpose_sub, transpose_one, ht]
    calc
      _ = 1 - P - P + P * P := by noncomm_ring
      _ = _ := by rw [hi]; abel
  have h := posSemidef_conjTranspose_mul_self (1 - P)
  simpa only [conjTranspose_eq_transpose_of_trivial, heq] using h

private lemma penrose_projection {ι σ : Type*} [Fintype ι] [Fintype σ]
    (B : Matrix σ ι ℝ) (X : Matrix ι σ ℝ) (hX : IsMoorePenrose B X) :
    (B * X) * (B * X) = B * X ∧ Xᵀ * (Bᵀ * B) * X = B * X := by
  have hi : (B * X) * (B * X) = B * X := by
    calc
      _ = (B * X * B) * X := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hX.1]
  refine ⟨hi, ?_⟩
  calc
    _ = (B * X)ᵀ * (B * X) := by simp only [transpose_mul, Matrix.mul_assoc]
    _ = (B * X) * (B * X) := by rw [hX.2.2.1]
    _ = B * X := hi

private lemma penrose_factorization {ι ρ σ : Type*} [Fintype ι] [Fintype ρ]
    [Fintype σ] [DecidableEq ι] [DecidableEq σ]
    (A : Matrix ρ ι ℝ) (B : Matrix σ ι ℝ) (X : Matrix ι σ ℝ)
    (hX : IsMoorePenrose B X) (hdom : (Bᵀ * B - Aᵀ * A).PosSemidef) :
    A = (A * X) * B ∧ (1 - (A * X)ᵀ * (A * X)).PosSemidef := by
  have hBZ : B * (X * B - 1) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hX.1, Matrix.mul_one, sub_self]
  have hAZ := gram_dom_kernel A B (X * B - 1) hdom hBZ
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, sub_eq_zero] at hAZ
  refine ⟨hAZ.symm, ?_⟩
  obtain ⟨hi, hp⟩ := penrose_projection B X hX
  have hcomp := projection_complement (B * X) hX.2.2.1 hi
  have hcong : (Xᵀ * (Bᵀ * B - Aᵀ * A) * X).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      hdom.conjTranspose_mul_mul_same X
  have hd : Xᵀ * (Bᵀ * B - Aᵀ * A) * X = B * X - (A * X)ᵀ * (A * X) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hp]
    simp only [transpose_mul, Matrix.mul_assoc]
  have heq : (1 - B * X) + Xᵀ * (Bᵀ * B - Aᵀ * A) * X =
      1 - (A * X)ᵀ * (A * X) := by rw [hd]; abel
  rw [← heq]
  exact hcomp.add hcong

private lemma quadratic_congruence {ι σ : Type*} [Fintype ι] [Fintype σ]
    (X : Matrix ι σ ℝ) (D : Matrix ι ι ℝ) (v : σ → ℝ) :
    star v ⬝ᵥ ((Xᵀ * D * X) *ᵥ v) =
      star (X *ᵥ v) ⬝ᵥ (D *ᵥ (X *ᵥ v)) := by
  simp only [star_trivial, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose,
    vecMul_vecMul]

private lemma penrose_factorization_strict {ι ρ σ : Type*} [Fintype ι] [Fintype ρ]
    [Fintype σ] [DecidableEq ι] [DecidableEq σ]
    (A : Matrix ρ ι ℝ) (B : Matrix σ ι ℝ) (X : Matrix ι σ ℝ)
    (hX : IsMoorePenrose B X) (hdom : (Bᵀ * B - Aᵀ * A).PosDef) :
    A = (A * X) * B ∧ (1 - (A * X)ᵀ * (A * X)).PosDef := by
  obtain ⟨hf, hs⟩ := penrose_factorization A B X hX hdom.posSemidef
  refine ⟨hf, Matrix.PosDef.of_dotProduct_mulVec_pos hs.isHermitian ?_⟩
  intro v hv
  by_cases hx : X *ᵥ v = 0
  · have hSv : (A * X) *ᵥ v = 0 := by
      rw [← mulVec_mulVec, hx, mulVec_zero]
    rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, hSv, mulVec_zero, sub_zero]
    exact dotProduct_star_self_pos_iff.mpr hv
  · obtain ⟨hi, hp⟩ := penrose_projection B X hX
    have hcomp := projection_complement (B * X) hX.2.2.1 hi
    have hq : 0 < star v ⬝ᵥ ((Xᵀ * (Bᵀ * B - Aᵀ * A) * X) *ᵥ v) := by
      rw [quadratic_congruence]
      exact hdom.dotProduct_mulVec_pos hx
    have hd : Xᵀ * (Bᵀ * B - Aᵀ * A) * X = B * X - (A * X)ᵀ * (A * X) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hp]
      simp only [transpose_mul, Matrix.mul_assoc]
    have heq : (1 - B * X) + Xᵀ * (Bᵀ * B - Aᵀ * A) * X =
        1 - (A * X)ᵀ * (A * X) := by rw [hd]; abel
    rw [← heq, add_mulVec, dotProduct_add]
    exact add_pos_of_nonneg_of_pos (hcomp.dotProduct_mulVec_nonneg v) hq

private lemma full_column_rank_injective {ι σ : Type*} [Fintype ι] [Fintype σ]
    (B : Matrix σ ι ℝ) (hB : B.rank = Fintype.card ι) :
    Function.Injective (fun v => B *ᵥ v) := by
  have hdim := B.mulVecLin.finrank_range_add_finrank_ker
  have hr : Module.finrank ℝ (LinearMap.range B.mulVecLin) = Fintype.card ι := hB
  rw [hr, Module.finrank_pi] at hdim
  have hz : Module.finrank ℝ (LinearMap.ker B.mulVecLin) = 0 := by omega
  have hk : LinearMap.ker B.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hz
  exact LinearMap.ker_eq_bot.mp hk

private lemma factor_gram_identity {ι ρ σ : Type*} [Fintype ι] [Fintype ρ]
    [Fintype σ] [DecidableEq σ]
    (A : Matrix ρ ι ℝ) (B : Matrix σ ι ℝ) (S : Matrix ρ σ ℝ)
    (hf : A = S * B) : Bᵀ * B - Aᵀ * A = Bᵀ * (1 - Sᵀ * S) * B := by
  rw [hf, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  simp only [transpose_mul, Matrix.mul_assoc]

theorem solution {ι ρ σ : Type*} [Fintype ι] [Fintype ρ] [Fintype σ]
    [DecidableEq ι] [DecidableEq ρ] [DecidableEq σ]
    (A : Matrix ρ ι ℝ) (B : Matrix σ ι ℝ) :
    ((Bᵀ * B - Aᵀ * A).PosSemidef ↔
        ∃ S : Matrix ρ σ ℝ, A = S * B ∧ (1 - Sᵀ * S).PosSemidef) ∧
    (B.rank = Fintype.card ι →
      ((Bᵀ * B - Aᵀ * A).PosDef ↔
        ∃ S : Matrix ρ σ ℝ, A = S * B ∧ (1 - Sᵀ * S).PosDef)) ∧
    ((-(Aᵀ * A - Bᵀ * B)).PosSemidef →
      A = (A * pinv B) * B ∧ (1 - (A * pinv B)ᵀ * (A * pinv B)).PosSemidef) ∧
    (B.rank = Fintype.card ι → (-(Aᵀ * A - Bᵀ * B)).PosDef →
      A = (A * pinv B) * B ∧ (1 - (A * pinv B)ᵀ * (A * pinv B)).PosDef) := by
  have hpinv := pinv_penrose B
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro hdom
    exact ⟨A * pinv B, penrose_factorization A B (pinv B) hpinv hdom⟩
  · rintro ⟨S, hf, hs⟩
    rw [factor_gram_identity A B S hf]
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      hs.conjTranspose_mul_mul_same B
  · intro hB
    constructor
    · intro hdom
      exact ⟨A * pinv B, penrose_factorization_strict A B (pinv B) hpinv hdom⟩
    · rintro ⟨S, hf, hs⟩
      rw [factor_gram_identity A B S hf]
      simpa only [conjTranspose_eq_transpose_of_trivial] using
        hs.conjTranspose_mul_mul_same (B := B) (full_column_rank_injective B hB)
  · intro hdom
    exact penrose_factorization A B (pinv B) hpinv (by simpa only [neg_sub] using hdom)
  · intro _ hdom
    exact penrose_factorization_strict A B (pinv B) hpinv (by simpa only [neg_sub] using hdom)

