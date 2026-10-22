-- Prove2me | solution 1 for QuadMatIneq.Petersen.schur_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:19:44.559683+00:00
-- url     : https://prove2.me/submissions/4827a90f-572e-4914-8b03-ec41a5e2c365

import Mathlib
import Definitions.Def_QuadMatIneq_Petersen_QMI
import Definitions.Def_QuadMatIneq_Petersen_Setup

set_option autoImplicit false
open Matrix QuadMatIneq.Petersen

theorem qmp_qid {n p : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (E : Matrix (Fin n) (Fin p) ℝ) (α : ℝ)
    (hα : 0 < α) (x : Fin n → ℝ) (y : Fin p → ℝ) :
    Sum.elim x y ⬝ᵥ ((Matrix.fromBlocks A (-E) (-Eᵀ) (α • (1 : Matrix (Fin p) (Fin p) ℝ))) *ᵥ Sum.elim x y)
      = x ⬝ᵥ (A - α⁻¹ • (E * Eᵀ)) *ᵥ x +
        α * ((y - α⁻¹ • (Eᵀ *ᵥ x)) ⬝ᵥ (y - α⁻¹ • (Eᵀ *ᵥ x))) := by
  rw [Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, sumElim_dotProduct_sumElim]
  have hu1 : x ⬝ᵥ E *ᵥ y = (Eᵀ *ᵥ x) ⬝ᵥ y := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  have hu2 : x ⬝ᵥ (E * Eᵀ) *ᵥ x = (Eᵀ *ᵥ x) ⬝ᵥ (Eᵀ *ᵥ x) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  simp only [Matrix.add_mulVec, Matrix.neg_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.sub_mulVec, dotProduct_add, dotProduct_sub, dotProduct_smul, dotProduct_neg,
    add_dotProduct, sub_dotProduct, smul_dotProduct, neg_dotProduct, smul_eq_mul, hu1, hu2]
  rw [dotProduct_comm y (Eᵀ *ᵥ x)]
  field_simp
  ring

theorem qmp_equiv {n p : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (E : Matrix (Fin n) (Fin p) ℝ) (α : ℝ)
    (hα : 0 < α) (hA : A.IsHermitian) :
    ((Matrix.fromBlocks A (-E) (-Eᵀ) (α • (1 : Matrix (Fin p) (Fin p) ℝ))).PosDef ↔
      (A - α⁻¹ • (E * Eᵀ)).PosDef) ∧
    ((Matrix.fromBlocks A (-E) (-Eᵀ) (α • (1 : Matrix (Fin p) (Fin p) ℝ))).PosSemidef ↔
      (A - α⁻¹ • (E * Eᵀ)).PosSemidef) := by
  have hPh : (Matrix.fromBlocks A (-E) (-Eᵀ) (α • (1 : Matrix (Fin p) (Fin p) ℝ))).IsHermitian := by
    rw [Matrix.isHermitian_fromBlocks_iff]
    refine ⟨hA, ?_, ?_, ?_⟩
    · simp [Matrix.conjTranspose_eq_transpose_of_trivial]
    · simp [Matrix.conjTranspose_eq_transpose_of_trivial]
    · ext i j; simp [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.one_apply, eq_comm]
  have hSh : (A - α⁻¹ • (E * Eᵀ)).IsHermitian := by
    refine hA.sub ?_
    have h1 : (E * Eᵀ).IsHermitian := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.isHermitian_mul_conjTranspose_self E
    show (α⁻¹ • (E * Eᵀ))ᴴ = α⁻¹ • (E * Eᵀ)
    rw [Matrix.conjTranspose_smul, star_trivial, h1.eq]
  have hq := qmp_qid A E α hα
  have key : ∀ z : Fin n ⊕ Fin p → ℝ, z ⬝ᵥ ((Matrix.fromBlocks A (-E) (-Eᵀ) (α • (1 : Matrix (Fin p) (Fin p) ℝ))) *ᵥ z)
      = (z ∘ Sum.inl) ⬝ᵥ (A - α⁻¹ • (E * Eᵀ)) *ᵥ (z ∘ Sum.inl) +
        α * (((z ∘ Sum.inr) - α⁻¹ • (Eᵀ *ᵥ (z ∘ Sum.inl))) ⬝ᵥ ((z ∘ Sum.inr) - α⁻¹ • (Eᵀ *ᵥ (z ∘ Sum.inl)))) := by
    intro z
    have := hq (z ∘ Sum.inl) (z ∘ Sum.inr)
    rwa [Sum.elim_comp_inl_inr] at this
  have hnn : ∀ v : Fin p → ℝ, 0 ≤ v ⬝ᵥ v := fun v => by simpa using dotProduct_star_self_nonneg v
  constructor
  · rw [Matrix.posDef_iff_dotProduct_mulVec, Matrix.posDef_iff_dotProduct_mulVec]
    constructor
    · rintro ⟨-, h⟩
      refine ⟨hSh, fun x hx => ?_⟩
      have hz : (Sum.elim x (α⁻¹ • (Eᵀ *ᵥ x)) : Fin n ⊕ Fin p → ℝ) ≠ 0 := by
        intro h0
        apply hx
        funext i
        have := congrFun h0 (Sum.inl i)
        simpa using this
      have := h hz
      rw [star_trivial, key] at this
      simpa using this
    · rintro ⟨-, h⟩
      refine ⟨hPh, fun z hz => ?_⟩
      rw [star_trivial, key]
      by_cases hx : (z ∘ Sum.inl) = 0
      · have hy : (z ∘ Sum.inr) ≠ 0 := by
          intro hy
          apply hz
          funext i
          rcases i with i | i
          · exact congrFun hx i
          · exact congrFun hy i
        rw [hx]
        simp only [Matrix.mulVec_zero, dotProduct_zero, zero_add, smul_zero, sub_zero]
        exact mul_pos hα (lt_of_le_of_ne (hnn _) (fun h0 => hy (dotProduct_self_eq_zero.mp h0.symm)))
      · have h1 := h hx
        rw [star_trivial] at h1
        have := mul_nonneg hα.le (hnn ((z ∘ Sum.inr) - α⁻¹ • (Eᵀ *ᵥ (z ∘ Sum.inl))))
        linarith
  · rw [Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.posSemidef_iff_dotProduct_mulVec]
    constructor
    · rintro ⟨-, h⟩
      refine ⟨hSh, fun x => ?_⟩
      have := h (Sum.elim x (α⁻¹ • (Eᵀ *ᵥ x)))
      rw [star_trivial, key] at this
      simpa using this
    · rintro ⟨-, h⟩
      refine ⟨hPh, fun z => ?_⟩
      rw [star_trivial, key]
      have h1 := h (z ∘ Sum.inl)
      rw [star_trivial] at h1
      have := mul_nonneg hα.le (hnn ((z ∘ Sum.inr) - α⁻¹ • (Eᵀ *ᵥ (z ∘ Sum.inl))))
      linarith

theorem solution {n p q : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (E : Matrix (Fin n) (Fin p) ℝ)
    (Fbar : Matrix (Fin q) (Fin q) ℝ) (G : Matrix (Fin q) (Fin n) ℝ)
    (hC : C.IsHermitian) (hFbar : Fbar.PosSemidef) (α : ℝ) (hα : 0 < α) :
    ((petersenM C E - α • petersenN Fbar G).PosDef ↔
      (-C - α • (Gᵀ * Fbar * G) - α⁻¹ • (E * Eᵀ)).PosDef) ∧
    ((petersenM C E - α • petersenN Fbar G).PosSemidef ↔
      (-C - α • (Gᵀ * Fbar * G) - α⁻¹ • (E * Eᵀ)).PosSemidef) := by
  have hMat : petersenM C E - α • petersenN Fbar G =
      Matrix.fromBlocks (-C - α • (Gᵀ * Fbar * G)) (-E) (-Eᵀ) (α • (1 : Matrix (Fin p) (Fin p) ℝ)) := by
    unfold petersenM petersenN
    ext (i | i) (j | j) <;> simp
  have hA : (-C - α • (Gᵀ * Fbar * G)).IsHermitian := by
    have h1 : (Gᵀ * Fbar * G).IsHermitian := by
      have := hFbar.conjTranspose_mul_mul_same G
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this.1
    refine hC.neg.sub ?_
    show (α • (Gᵀ * Fbar * G))ᴴ = α • (Gᵀ * Fbar * G)
    rw [Matrix.conjTranspose_smul, star_trivial, h1.eq]
  rw [hMat]
  exact qmp_equiv _ E α hα hA
