-- Prove2me | solution 1 for TroppMatrixConcentration.dilation_identities
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T01:11:12.321116+00:00
-- url     : https://prove2.me/submissions/651fc73b-a55e-4412-b3ba-5852578b30f1

import Definitions.Def_TroppMatrixConcentration_dilation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

open scoped Matrix.Norms.L2Operator

namespace TroppMatrixConcentration.DilationIdentities

open Matrix

/-- Upper bound for the L2 operator norm via a bound on vectors. -/
lemma opNorm_le_of {p q : Type*} [Fintype p] [Fintype q] [DecidableEq q]
    (M : Matrix p q ℂ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : q → ℂ, ‖(WithLp.toLp 2 (M *ᵥ x) : EuclideanSpace ℂ p)‖ ≤
      c * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ q)‖) : ‖M‖ ≤ c := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  simpa [Matrix.toLpLin_apply] using h (WithLp.ofLp x)

lemma norm_mulVec_le {p q : Type*} [Fintype p] [Fintype q] [DecidableEq q]
    (M : Matrix p q ℂ) (x : q → ℂ) :
    ‖(WithLp.toLp 2 (M *ᵥ x) : EuclideanSpace ℂ p)‖ ≤
      ‖M‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ q)‖ := by
  simpa using Matrix.l2_opNorm_mulVec M (WithLp.toLp 2 x)

lemma norm_sq_elim {m n : Type*} [Fintype m] [Fintype n] (u : m → ℂ) (w : n → ℂ) :
    ‖(WithLp.toLp 2 (Sum.elim u w) : EuclideanSpace ℂ (m ⊕ n))‖ ^ 2 =
      ‖(WithLp.toLp 2 u : EuclideanSpace ℂ m)‖ ^ 2 +
        ‖(WithLp.toLp 2 w : EuclideanSpace ℂ n)‖ ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]

lemma isHermitian {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : (dilation A).IsHermitian := by
  unfold dilation
  simp [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose]

lemma sq_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    (dilation A) ^ 2 = Matrix.fromBlocks (A * A.conjTranspose) 0 0
      (A.conjTranspose * A) := by
  unfold dilation
  simp [sq, Matrix.fromBlocks_multiply]

lemma neg_mem_spectrum {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) {r : ℝ}
    (hr : r ∈ spectrum ℝ (dilation A)) : -r ∈ spectrum ℝ (dilation A) := by
  set S : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ := Matrix.fromBlocks 1 0 0 (-1) with hS
  have hSS : S * S = 1 := by
    simp [hS, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  let u : (Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)ˣ := ⟨S, S, hSS, hSS⟩
  have hconj : (u : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) * dilation A *
      (↑(u⁻¹) : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) = -dilation A := by
    show S * dilation A * S = -dilation A
    simp [hS, dilation, Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg]
  have h1 : spectrum ℝ (-dilation A) = spectrum ℝ (dilation A) := by
    rw [← hconj, spectrum.units_conjugate]
  rw [← h1, ← spectrum.neg_eq, Set.mem_neg, neg_neg]
  exact hr

lemma lambdaMax_eq {m n : ℕ} [NeZero m] [NeZero n] (A : Matrix (Fin m) (Fin n) ℂ) :
    lambdaMax (dilation A) = spectralNorm (dilation A) := by
  have hsa : IsSelfAdjoint (dilation A) := isHermitian A
  have hmem : ‖dilation A‖ ∈ spectrum ℝ (dilation A) := by
    rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum hsa with h | h
    · exact h
    · simpa using neg_mem_spectrum A h
  unfold lambdaMax spectralNorm
  refine IsGreatest.csSup_eq ⟨hmem, fun x hx => ?_⟩
  have := spectrum.norm_le_norm_of_mem hx
  exact (le_abs_self x).trans (by simpa using this)

lemma spectralNorm_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    spectralNorm (dilation A) = spectralNorm A := by
  unfold spectralNorm
  apply le_antisymm
  · refine opNorm_le_of _ (norm_nonneg _) fun x => ?_
    have hx : x = Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) := by
      ext i; cases i <;> rfl
    have hHx : dilation A *ᵥ x = Sum.elim (A *ᵥ (x ∘ Sum.inr)) (Aᴴ *ᵥ (x ∘ Sum.inl)) := by
      simp [dilation, Matrix.fromBlocks_mulVec]
    rw [hHx]
    have h1 := norm_mulVec_le A (x ∘ Sum.inr)
    have h2 := norm_mulVec_le Aᴴ (x ∘ Sum.inl)
    rw [Matrix.l2_opNorm_conjTranspose] at h2
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
    rw [norm_sq_elim, mul_pow, hx, norm_sq_elim]
    simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr] at h1 h2 ⊢
    nlinarith [norm_nonneg (WithLp.toLp 2 (A *ᵥ fun i => x (Sum.inr i)) : EuclideanSpace ℂ (Fin m)),
      norm_nonneg (WithLp.toLp 2 (Aᴴ *ᵥ fun i => x (Sum.inl i)) : EuclideanSpace ℂ (Fin n)),
      mul_le_mul h1 h1 (norm_nonneg _) (by positivity),
      mul_le_mul h2 h2 (norm_nonneg _) (by positivity)]
  · refine opNorm_le_of _ (norm_nonneg _) fun y => ?_
    have h := norm_mulVec_le (dilation A) (Sum.elim 0 y)
    have hHy : dilation A *ᵥ Sum.elim 0 y = Sum.elim (A *ᵥ y) 0 := by
      ext i; cases i <;> simp [dilation,
        Matrix.mulVec, dotProduct]
    rw [hHy] at h
    have e1 : ‖(WithLp.toLp 2 (Sum.elim (A *ᵥ y) 0) : EuclideanSpace ℂ (Fin m ⊕ Fin n))‖ =
        ‖(WithLp.toLp 2 (A *ᵥ y) : EuclideanSpace ℂ (Fin m))‖ := by
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_elim]; simp
    have e2 : ‖(WithLp.toLp 2 (Sum.elim 0 y) : EuclideanSpace ℂ (Fin m ⊕ Fin n))‖ =
        ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin n))‖ := by
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_elim]; simp
    rwa [e1, e2] at h

end TroppMatrixConcentration.DilationIdentities

open TroppMatrixConcentration

theorem solution {m n : ℕ} [NeZero m] [NeZero n]
    (A : Matrix (Fin m) (Fin n) ℂ) :
    (dilation A).IsHermitian ∧
    (dilation A) ^ 2 = Matrix.fromBlocks (A * A.conjTranspose) 0 0
      (A.conjTranspose * A) ∧
    lambdaMax (dilation A) = spectralNorm (dilation A) ∧
    spectralNorm (dilation A) = spectralNorm A :=
  ⟨DilationIdentities.isHermitian A, DilationIdentities.sq_eq A,
    DilationIdentities.lambdaMax_eq A, DilationIdentities.spectralNorm_eq A⟩
