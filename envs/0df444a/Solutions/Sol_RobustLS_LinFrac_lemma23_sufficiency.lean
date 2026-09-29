-- Prove2me | solution 1 for RobustLS.LinFrac.lemma23_sufficiency
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:50:59.265131+00:00
-- url     : https://prove2.me/submissions/ddb9fa71-c372-42f2-a81f-86b22dd3183c

import Mathlib
import Definitions.Def_RobustLS_LinFrac_Core

open Matrix

namespace RobustLS.LinFrac

theorem aux_l23s_normsq {a : Type*} [Fintype a] (w : a → ℝ) :
    ‖(WithLp.toLp 2 w : EuclideanSpace ℝ a)‖ ^ 2 = w ⬝ᵥ w := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, sq]

theorem aux_l23s_bound {a b : ℕ} (X : Matrix (Fin a) (Fin b) ℝ) (v : Fin b → ℝ) :
    (X *ᵥ v) ⬝ᵥ (X *ᵥ v) ≤ specNorm X ^ 2 * (v ⬝ᵥ v) := by
  have h := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X)).le_opNorm
    (WithLp.toLp 2 v)
  have h' : ‖(WithLp.toLp 2 (X *ᵥ v) : EuclideanSpace ℝ (Fin a))‖ ≤
      specNorm X * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin b))‖ := h
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h' 2
  rw [mul_pow, aux_l23s_normsq, aux_l23s_normsq] at h2
  exact h2

theorem aux_l23s_specNorm_nonneg {a b : ℕ} (X : Matrix (Fin a) (Fin b) ℝ) :
    0 ≤ specNorm X := norm_nonneg _

theorem aux_l23s_specNorm_transpose {a b : ℕ} (X : Matrix (Fin a) (Fin b) ℝ) :
    specNorm Xᵀ = specNorm X := by
  have := Matrix.l2_opNorm_conjTranspose (𝕜 := ℝ) X
  rw [conjTranspose_eq_transpose_of_trivial] at this
  exact this

theorem aux_l23s_dot {a b : Type*} [Fintype a] [Fintype b] (A : Matrix a b ℝ) (x : a → ℝ)
    (y : b → ℝ) : x ⬝ᵥ (A *ᵥ y) = (Aᵀ *ᵥ x) ⬝ᵥ y := by
  rw [dotProduct_mulVec, mulVec_transpose]

theorem aux_l23s_dotself_nonneg {a : Type*} [Fintype a] (v : a → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Fintype.sum_nonneg fun i => mul_self_nonneg (v i)

open scoped MatrixOrder in
theorem aux_l23s_commute_psd {N : ℕ} (S C : Matrix (Fin N) (Fin N) ℝ) (hS : S.PosSemidef)
    (hC : C.PosSemidef) (h : S * C = C * S) : (S * C).PosSemidef :=
  (Commute.mul_nonneg hS.nonneg hC.nonneg h).posSemidef

theorem aux_l23s_Sineq {N : ℕ} (S Δ : Matrix (Fin N) (Fin N) ℝ) (hS : S.PosSemidef)
    (hSsym : S = Sᵀ) (hSΔ : S * Δ = Δ * S) (hΔ : specNorm Δ ≤ 1) (v : Fin N → ℝ) :
    (Δᵀ *ᵥ v) ⬝ᵥ (S *ᵥ (Δᵀ *ᵥ v)) ≤ v ⬝ᵥ (S *ᵥ v) := by
  set C : Matrix (Fin N) (Fin N) ℝ := 1 - Δ * Δᵀ with hC
  have hCpsd : C.PosSemidef := by
    apply PosSemidef.of_dotProduct_mulVec_nonneg
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hC, transpose_sub, transpose_one,
        transpose_mul, transpose_transpose]
    · intro x
      rw [star_trivial, hC, sub_mulVec, one_mulVec, dotProduct_sub, ← mulVec_mulVec,
        aux_l23s_dot Δ x]
      have hb := aux_l23s_bound Δᵀ x
      rw [aux_l23s_specNorm_transpose] at hb
      have hsd := aux_l23s_specNorm_nonneg Δ
      have hsd' : specNorm Δ ^ 2 ≤ 1 := by nlinarith
      have := aux_l23s_dotself_nonneg x
      nlinarith
  have hSΔt : S * Δᵀ = Δᵀ * S := by
    have := congrArg transpose hSΔ
    rw [transpose_mul, transpose_mul, ← hSsym] at this
    exact this.symm
  have hcomm : S * C = C * S := by
    rw [hC, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
    congr 1
    rw [← Matrix.mul_assoc, hSΔ, Matrix.mul_assoc, hSΔt, Matrix.mul_assoc]
  have hpsd := aux_l23s_commute_psd S C hS hCpsd hcomm
  have h1 := hpsd.dotProduct_mulVec_nonneg v
  rw [star_trivial, hC, Matrix.mul_sub, Matrix.mul_one, sub_mulVec, dotProduct_sub] at h1
  have h2 : (Δᵀ *ᵥ v) ⬝ᵥ (S *ᵥ (Δᵀ *ᵥ v)) = v ⬝ᵥ ((S * (Δ * Δᵀ)) *ᵥ v) := by
    rw [← aux_l23s_dot Δ v, mulVec_mulVec, mulVec_mulVec, ← Matrix.mul_assoc S, hSΔ]
  linarith


theorem aux_l23s_form {d N : ℕ} (T₁ : Matrix (Fin d) (Fin d) ℝ)
    (T₂ : Matrix (Fin d) (Fin N) ℝ) (T₃ : Matrix (Fin N) (Fin d) ℝ)
    (T₄ S G : Matrix (Fin N) (Fin N) ℝ) (hSsym : S = Sᵀ) (hGskew : G = -Gᵀ)
    (ξ : Fin d → ℝ) (p : Fin N → ℝ) :
    Sum.elim ξ p ⬝ᵥ (lemma23Block T₁ T₂ T₃ T₄ S G *ᵥ Sum.elim ξ p) =
      ξ ⬝ᵥ (T₁ *ᵥ ξ) + 2 * ((T₃ *ᵥ ξ) ⬝ᵥ p)
      - (T₂ᵀ *ᵥ ξ + T₄ᵀ *ᵥ p) ⬝ᵥ (S *ᵥ (T₂ᵀ *ᵥ ξ + T₄ᵀ *ᵥ p)) + p ⬝ᵥ (S *ᵥ p)
      + 2 * ((T₂ᵀ *ᵥ ξ + T₄ᵀ *ᵥ p) ⬝ᵥ (G *ᵥ p)) := by
  have hS : ∀ x y : Fin N → ℝ, x ⬝ᵥ (S *ᵥ y) = y ⬝ᵥ (S *ᵥ x) := by
    intro x y
    rw [aux_l23s_dot S x y, ← hSsym, dotProduct_comm]
  have hG : ∀ x y : Fin N → ℝ, x ⬝ᵥ (G *ᵥ y) = -(y ⬝ᵥ (G *ᵥ x)) := by
    intro x y
    have h : Gᵀ = -G := by nth_rewrite 2 [hGskew]; rw [neg_neg]
    rw [aux_l23s_dot G x y, h, neg_mulVec, neg_dotProduct, dotProduct_comm]
  rw [lemma23Block, fromBlocks_mulVec, sumElim_dotProduct_sumElim, Sum.elim_comp_inl,
    Sum.elim_comp_inr]
  simp only [sub_mulVec, add_mulVec, dotProduct_add, dotProduct_sub, add_dotProduct,
    mulVec_add, ← mulVec_mulVec]
  set a := T₂ᵀ *ᵥ ξ with ha
  set b := T₄ᵀ *ᵥ p with hb
  rw [aux_l23s_dot T₂ ξ (S *ᵥ a), aux_l23s_dot T₂ ξ (S *ᵥ b), aux_l23s_dot T₂ ξ (G *ᵥ p),
    aux_l23s_dot T₃ᵀ ξ p, transpose_transpose, aux_l23s_dot T₄ p (S *ᵥ a),
    aux_l23s_dot T₄ p (S *ᵥ b), aux_l23s_dot T₄ p (G *ᵥ p), ← ha, ← hb,
    dotProduct_comm p (T₃ *ᵥ ξ), hS b a, hG p a, hG p b]
  ring

end RobustLS.LinFrac

open RobustLS.LinFrac

theorem solution {d N : ℕ} (𝒟 : Submodule ℝ (Matrix (Fin N) (Fin N) ℝ))
    (T₁ : Matrix (Fin d) (Fin d) ℝ) (hT₁ : T₁ = T₁ᵀ)
    (T₂ : Matrix (Fin d) (Fin N) ℝ) (T₃ : Matrix (Fin N) (Fin d) ℝ)
    (T₄ S G : Matrix (Fin N) (Fin N) ℝ) (hS : S ∈ symCommutant 𝒟) (hG : G ∈ skewCommutant 𝒟)
    (hGΔ : ∀ Δ ∈ 𝒟, (G * Δ)ᵀ = -(G * Δ)) (hSpos : S.PosDef)
    (hblock : (lemma23Block T₁ T₂ T₃ T₄ S G).PosDef) :
    ∀ Δ ∈ 𝒟, specNorm Δ ≤ 1 →
      (1 - T₄ * Δ).det ≠ 0 ∧ (lftT T₁ T₂ T₃ T₄ Δ).PosDef := by
  intro Δ hΔD hΔ
  obtain ⟨hScomm, hSsym⟩ := hS
  obtain ⟨hGcomm, hGskew⟩ := hG
  have hSΔ : S * Δ = Δ * S := hScomm Δ hΔD
  have hGΔc : G * Δ = Δ * G := hGcomm Δ hΔD
  have hGΔs := hGΔ Δ hΔD
  have hGt' : Gᵀ = -G := by nth_rewrite 2 [hGskew]; rw [neg_neg]
  have h1 : (G * Δᵀ)ᵀ = -(G * Δ) := by
    rw [transpose_mul, transpose_transpose, hGt', Matrix.mul_neg, hGΔc]
  have hGt : G * Δᵀ = G * Δ := by
    rw [← transpose_transpose (G * Δᵀ), h1, transpose_neg, hGΔs, neg_neg]
  have hzero : ∀ v : Fin N → ℝ, v ⬝ᵥ (G *ᵥ (Δᵀ *ᵥ v)) = 0 := by
    intro v
    rw [mulVec_mulVec, hGt]
    have h := aux_l23s_dot (G * Δ) v v
    rw [hGΔs, neg_mulVec, neg_dotProduct, dotProduct_comm] at h
    rw [dotProduct_comm]
    linarith
  have hkey : ∀ (ξ : Fin d → ℝ) (p : Fin N → ℝ), p = Δᵀ *ᵥ (T₂ᵀ *ᵥ ξ + T₄ᵀ *ᵥ p) →
      Sum.elim ξ p ⬝ᵥ (lemma23Block T₁ T₂ T₃ T₄ S G *ᵥ Sum.elim ξ p) ≤
        ξ ⬝ᵥ (T₁ *ᵥ ξ) + 2 * ((T₃ *ᵥ ξ) ⬝ᵥ p) := by
    intro ξ p hp
    rw [aux_l23s_form T₁ T₂ T₃ T₄ S G hSsym hGskew ξ p]
    set v := T₂ᵀ *ᵥ ξ + T₄ᵀ *ᵥ p with hv
    have h1 := aux_l23s_Sineq S Δ hSpos.posSemidef hSsym hSΔ hΔ v
    rw [← hp] at h1
    have h2 := hzero v
    rw [← hp] at h2
    linarith
  have hdet : (1 - T₄ * Δ).det ≠ 0 := by
    intro h0
    have h0' : (1 - T₄ * Δ)ᵀ.det = 0 := by rw [det_transpose]; exact h0
    obtain ⟨p, hp0, hMp⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0'
    have hp : p = Δᵀ *ᵥ (T₂ᵀ *ᵥ 0 + T₄ᵀ *ᵥ p) := by
      rw [mulVec_zero, zero_add, mulVec_mulVec]
      rw [transpose_sub, transpose_one, transpose_mul, sub_mulVec, one_mulVec] at hMp
      exact sub_eq_zero.mp hMp
    have hk := hkey 0 p hp
    have hne : Sum.elim (0 : Fin d → ℝ) p ≠ 0 := by
      intro h
      apply hp0
      funext i
      have := congrFun h (Sum.inr i)
      simpa using this
    have hpos := hblock.dotProduct_mulVec_pos hne
    rw [star_trivial] at hpos
    simp only [mulVec_zero, zero_dotProduct, dotProduct_zero, mul_zero, add_zero] at hk
    linarith
  refine ⟨hdet, ?_⟩
  set M := 1 - T₄ * Δ with hM
  have hlft : lftT T₁ T₂ T₃ T₄ Δ = T₁ + (T₂ * Δ * M⁻¹) * T₃ + T₃ᵀ * (T₂ * Δ * M⁻¹)ᵀ := by
    simp only [lftT, transpose_mul, Matrix.mul_assoc]
    rfl
  rw [hlft]
  apply PosDef.of_dotProduct_mulVec_pos
  · show (T₁ + (T₂ * Δ * M⁻¹) * T₃ + T₃ᵀ * (T₂ * Δ * M⁻¹)ᵀ)ᴴ = _
    rw [conjTranspose_eq_transpose_of_trivial]
    simp only [transpose_add, transpose_mul, transpose_transpose]
    rw [← hT₁]
    simp only [Matrix.mul_assoc]
    abel
  intro x hx
  rw [star_trivial]
  set Nm := T₂ * Δ * M⁻¹ with hN
  set u := Nmᵀ *ᵥ x with hu
  have hgoal : x ⬝ᵥ ((T₁ + Nm * T₃ + T₃ᵀ * Nmᵀ) *ᵥ x)
      = x ⬝ᵥ (T₁ *ᵥ x) + 2 * ((T₃ *ᵥ x) ⬝ᵥ u) := by
    rw [add_mulVec, add_mulVec, dotProduct_add, dotProduct_add, ← mulVec_mulVec x Nm T₃,
      ← mulVec_mulVec x T₃ᵀ Nmᵀ, aux_l23s_dot Nm, aux_l23s_dot T₃ᵀ, transpose_transpose, ← hu,
      dotProduct_comm u]
    ring
  rw [hgoal]
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
  have hk := hkey x u hu2
  have hne : Sum.elim x u ≠ 0 := by
    intro h
    apply hx
    funext i
    have := congrFun h (Sum.inl i)
    simpa using this
  have hpos := hblock.dotProduct_mulVec_pos hne
  rw [star_trivial] at hpos
  linarith
