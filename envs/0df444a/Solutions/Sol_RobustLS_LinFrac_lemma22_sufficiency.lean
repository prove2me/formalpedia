-- Prove2me | solution 1 for RobustLS.LinFrac.lemma22_sufficiency
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:49:33.955347+00:00
-- url     : https://prove2.me/submissions/6da22708-3b00-4940-b62f-bce3cd1b8924

import Mathlib
import Definitions.Def_RobustLS_LinFrac_Core

open Matrix

namespace RobustLS.LinFrac

theorem aux_l22s_normsq {a : Type*} [Fintype a] (w : a → ℝ) :
    ‖(WithLp.toLp 2 w : EuclideanSpace ℝ a)‖ ^ 2 = w ⬝ᵥ w := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, sq]

theorem aux_l22s_bound {a b : ℕ} (X : Matrix (Fin a) (Fin b) ℝ) (v : Fin b → ℝ) :
    (X *ᵥ v) ⬝ᵥ (X *ᵥ v) ≤ specNorm X ^ 2 * (v ⬝ᵥ v) := by
  have h := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X)).le_opNorm
    (WithLp.toLp 2 v)
  have h' : ‖(WithLp.toLp 2 (X *ᵥ v) : EuclideanSpace ℝ (Fin a))‖ ≤
      specNorm X * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin b))‖ := h
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h' 2
  rw [mul_pow, aux_l22s_normsq, aux_l22s_normsq] at h2
  exact h2

theorem aux_l22s_specNorm_nonneg {a b : ℕ} (X : Matrix (Fin a) (Fin b) ℝ) :
    0 ≤ specNorm X := norm_nonneg _

theorem aux_l22s_specNorm_transpose {a b : ℕ} (X : Matrix (Fin a) (Fin b) ℝ) :
    specNorm Xᵀ = specNorm X := by
  have := Matrix.l2_opNorm_conjTranspose (𝕜 := ℝ) X
  rw [conjTranspose_eq_transpose_of_trivial] at this
  exact this

theorem aux_l22s_dot {a b : Type*} [Fintype a] [Fintype b] (A : Matrix a b ℝ) (x : a → ℝ)
    (y : b → ℝ) : x ⬝ᵥ (A *ᵥ y) = (Aᵀ *ᵥ x) ⬝ᵥ y := by
  rw [dotProduct_mulVec, mulVec_transpose]

theorem aux_l22s_dotself_nonneg {a : Type*} [Fintype a] (v : a → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Fintype.sum_nonneg fun i => mul_self_nonneg (v i)

theorem aux_l22s_det {k l : ℕ} (T₄ : Matrix (Fin l) (Fin k) ℝ) (hT₄ : specNorm T₄ < 1)
    (Δ : Matrix (Fin k) (Fin l) ℝ) (hΔ : specNorm Δ ≤ 1) : (1 - T₄ * Δ).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv0, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hv : v = T₄ *ᵥ (Δ *ᵥ v) := by
    rw [sub_mulVec, one_mulVec, ← mulVec_mulVec] at hMv
    exact sub_eq_zero.mp hMv
  have h1 := aux_l22s_bound Δ v
  have h2 := aux_l22s_bound T₄ (Δ *ᵥ v)
  rw [← hv] at h2
  have hpos : 0 < v ⬝ᵥ v := by
    rcases (aux_l22s_dotself_nonneg v).lt_or_eq with h | h
    · exact h
    · exact absurd (dotProduct_self_eq_zero.mp h.symm) hv0
  have hs4 := aux_l22s_specNorm_nonneg T₄
  have hsd := aux_l22s_specNorm_nonneg Δ
  have hs4' : specNorm T₄ ^ 2 < 1 := by nlinarith
  have hsd' : specNorm Δ ^ 2 ≤ 1 := by nlinarith
  have h3 : specNorm T₄ ^ 2 * ((Δ *ᵥ v) ⬝ᵥ (Δ *ᵥ v)) ≤ specNorm T₄ ^ 2 * (v ⬝ᵥ v) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    nlinarith
  nlinarith

end RobustLS.LinFrac

open RobustLS.LinFrac

theorem solution {d k l : ℕ} (T₁ : Matrix (Fin d) (Fin d) ℝ) (hT₁ : T₁ = T₁ᵀ)
    (T₂ : Matrix (Fin d) (Fin k) ℝ) (T₃ : Matrix (Fin l) (Fin d) ℝ)
    (T₄ : Matrix (Fin l) (Fin k) ℝ) (hT₄ : specNorm T₄ < 1) (τ : ℝ) (hτ : 0 ≤ τ)
    (h10 : (lemma22Block T₁ T₂ T₃ T₄ τ).PosSemidef) :
    ∀ Δ : Matrix (Fin k) (Fin l) ℝ, specNorm Δ ≤ 1 →
      (1 - T₄ * Δ).det ≠ 0 ∧ (lftT T₁ T₂ T₃ T₄ Δ).PosSemidef := by
  intro Δ hΔ
  have hdet := aux_l22s_det T₄ hT₄ Δ hΔ
  refine ⟨hdet, ?_⟩
  set M := 1 - T₄ * Δ with hM
  have hlft : lftT T₁ T₂ T₃ T₄ Δ = T₁ + (T₂ * Δ * M⁻¹) * T₃ + T₃ᵀ * (T₂ * Δ * M⁻¹)ᵀ := by
    simp only [lftT, transpose_mul, Matrix.mul_assoc]
    rfl
  rw [hlft]
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · show (T₁ + (T₂ * Δ * M⁻¹) * T₃ + T₃ᵀ * (T₂ * Δ * M⁻¹)ᵀ)ᴴ = _
    rw [conjTranspose_eq_transpose_of_trivial]
    simp only [transpose_add, transpose_mul, transpose_transpose]
    rw [← hT₁]
    simp only [Matrix.mul_assoc]
    abel
  intro x
  rw [star_trivial]
  set N := T₂ * Δ * M⁻¹ with hN
  set u := Nᵀ *ᵥ x with hu
  have hgoal : x ⬝ᵥ ((T₁ + N * T₃ + T₃ᵀ * Nᵀ) *ᵥ x)
      = x ⬝ᵥ (T₁ *ᵥ x) + 2 * ((T₃ *ᵥ x) ⬝ᵥ u) := by
    rw [add_mulVec, add_mulVec, dotProduct_add, dotProduct_add, ← mulVec_mulVec x N T₃,
      ← mulVec_mulVec x T₃ᵀ Nᵀ, aux_l22s_dot N, aux_l22s_dot T₃ᵀ, transpose_transpose, ← hu,
      dotProduct_comm u]
    ring
  rw [hgoal]
  -- the relation u = Δᵀ (T₂ᵀ x + T₄ᵀ u)
  have hinv : Mᵀ * (M⁻¹)ᵀ = 1 := by
    rw [← transpose_mul, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), transpose_one]
  have hMu : Mᵀ *ᵥ u = Δᵀ *ᵥ (T₂ᵀ *ᵥ x) := by
    rw [hu, mulVec_mulVec, mulVec_mulVec, hN, transpose_mul, transpose_mul,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have hMt : Mᵀ = 1 - Δᵀ * T₄ᵀ := by
    rw [hM, transpose_sub, transpose_one, transpose_mul]
  have hu2 : u = Δᵀ *ᵥ (T₂ᵀ *ᵥ x + T₄ᵀ *ᵥ u) := by
    rw [hMt, sub_mulVec, one_mulVec, ← mulVec_mulVec] at hMu
    rw [mulVec_add, ← hMu]
    abel
  set w := T₂ᵀ *ᵥ x + T₄ᵀ *ᵥ u with hw
  have huw : u ⬝ᵥ u ≤ w ⬝ᵥ w := by
    have hb := aux_l22s_bound Δᵀ w
    rw [← hu2, aux_l22s_specNorm_transpose] at hb
    have hsd := aux_l22s_specNorm_nonneg Δ
    have hsd' : specNorm Δ ^ 2 ≤ 1 := by nlinarith
    have := aux_l22s_dotself_nonneg w
    nlinarith
  -- the block quadratic form
  have hy := h10.dotProduct_mulVec_nonneg (Sum.elim x u)
  rw [star_trivial, lemma22Block, fromBlocks_mulVec, sumElim_dotProduct_sumElim,
    Sum.elim_comp_inl, Sum.elim_comp_inr] at hy
  simp only [sub_mulVec, smul_mulVec, dotProduct_add, dotProduct_sub,
    dotProduct_smul, one_mulVec, ← mulVec_mulVec, smul_eq_mul] at hy
  rw [aux_l22s_dot T₂ x (T₂ᵀ *ᵥ x), aux_l22s_dot T₃ᵀ x u, transpose_transpose,
    aux_l22s_dot T₂ x (T₄ᵀ *ᵥ u), aux_l22s_dot T₄ u (T₂ᵀ *ᵥ x),
    aux_l22s_dot T₄ u (T₄ᵀ *ᵥ u)] at hy
  have hww : w ⬝ᵥ w = (T₂ᵀ *ᵥ x) ⬝ᵥ (T₂ᵀ *ᵥ x) + 2 * ((T₂ᵀ *ᵥ x) ⬝ᵥ (T₄ᵀ *ᵥ u))
      + (T₄ᵀ *ᵥ u) ⬝ᵥ (T₄ᵀ *ᵥ u) := by
    rw [hw, add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm (T₄ᵀ *ᵥ u)]
    ring
  have hcomm : u ⬝ᵥ (T₃ *ᵥ x) = (T₃ *ᵥ x) ⬝ᵥ u := dotProduct_comm _ _
  have hcomm2 : (T₄ᵀ *ᵥ u) ⬝ᵥ (T₂ᵀ *ᵥ x) = (T₂ᵀ *ᵥ x) ⬝ᵥ (T₄ᵀ *ᵥ u) := dotProduct_comm _ _
  have hτuw := mul_le_mul_of_nonneg_left huw hτ
  rw [hww] at hτuw
  nlinarith
