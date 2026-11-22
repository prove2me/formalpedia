-- Prove2me | solution 1 for PQNormIPM1352.Main.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T08:46:45.607067+00:00
-- url     : https://prove2.me/submissions/9f4ba403-ed4a-4c4a-acd8-d75618da04dc

import Mathlib

open Matrix

theorem solution {S₁ S₂ : Type} [Fintype S₁] [Fintype S₂] [DecidableEq S₁] [DecidableEq S₂]
    (A : Matrix (S₁ ⊕ S₂) (S₁ ⊕ S₂) ℝ) (hA : A.PosDef) (x₁ : S₁ → ℝ) :
    IsLeast {t : ℝ | ∃ x₂ : S₂ → ℝ, t = Sum.elim x₁ x₂ ⬝ᵥ (A *ᵥ Sum.elim x₁ x₂)}
        (x₁ ⬝ᵥ ((A.toBlocks₁₁ - A.toBlocks₁₂ * A.toBlocks₂₂⁻¹ * A.toBlocks₂₁) *ᵥ x₁)) ∧
      Sum.elim x₁ (-(A.toBlocks₂₂⁻¹ * A.toBlocks₂₁) *ᵥ x₁) ⬝ᵥ
          (A *ᵥ Sum.elim x₁ (-(A.toBlocks₂₂⁻¹ * A.toBlocks₂₁) *ᵥ x₁)) =
        x₁ ⬝ᵥ ((A.toBlocks₁₁ - A.toBlocks₁₂ * A.toBlocks₂₂⁻¹ * A.toBlocks₂₁) *ᵥ x₁) := by
  classical
  set A₁₁ := A.toBlocks₁₁ with hA₁₁
  set A₁₂ := A.toBlocks₁₂ with hA₁₂
  set A₂₁ := A.toBlocks₂₁ with hA₂₁
  set A₂₂ := A.toBlocks₂₂ with hA₂₂def
  set S := A₁₁ - A₁₂ * A₂₂⁻¹ * A₂₁ with hS
  have hblocks : A = fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ := (Matrix.fromBlocks_toBlocks A).symm
  have hHerm : (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).IsHermitian := by rw [← hblocks]; exact hA.1
  obtain ⟨-, hA₁₂H, -, hD⟩ := Matrix.isHermitian_fromBlocks_iff.mp hHerm
  have hA₂₂ : A₂₂.PosDef := by
    have h := hA.submatrix (Sum.inr_injective : Function.Injective (Sum.inr : S₂ → S₁ ⊕ S₂))
    simpa [A₂₂, Matrix.toBlocks₂₂, Matrix.submatrix] using h
  have hunit : IsUnit A₂₂.det := (Matrix.isUnit_iff_isUnit_det A₂₂).mp hA₂₂.isUnit
  letI : Invertible A₂₂.det := hunit.invertible
  letI : Invertible A₂₂ := Matrix.invertibleOfDetInvertible A₂₂
  have hQ : ∀ x₂ : S₂ → ℝ,
      Sum.elim x₁ x₂ ⬝ᵥ (A *ᵥ Sum.elim x₁ x₂) =
        (x₂ + (A₂₂⁻¹ * A₂₁) *ᵥ x₁) ⬝ᵥ (A₂₂ *ᵥ (x₂ + (A₂₂⁻¹ * A₂₁) *ᵥ x₁)) +
          x₁ ⬝ᵥ (S *ᵥ x₁) := by
    intro x₂
    have h := Matrix.schur_complement_eq₂₂ A₁₁ A₁₂ x₁ x₂ (D := A₂₂) hD
    rw [hA₁₂H, ← hblocks] at h
    simp only [Matrix.dotProduct_mulVec]
    simpa [hS, star_trivial, add_comm] using h
  have hQ0 : Sum.elim x₁ ((-(A₂₂⁻¹ * A₂₁)) *ᵥ x₁) ⬝ᵥ
      (A *ᵥ Sum.elim x₁ ((-(A₂₂⁻¹ * A₂₁)) *ᵥ x₁)) = x₁ ⬝ᵥ (S *ᵥ x₁) := by
    rw [hQ]
    have hzero : (-(A₂₂⁻¹ * A₂₁)) *ᵥ x₁ + (A₂₂⁻¹ * A₂₁) *ᵥ x₁ = 0 := by
      rw [Matrix.neg_mulVec, neg_add_cancel]
    simp [hzero]
  have hnonneg : ∀ w : S₂ → ℝ, 0 ≤ w ⬝ᵥ (A₂₂ *ᵥ w) := by
    intro w
    have h := hA₂₂.posSemidef.dotProduct_mulVec_nonneg w
    simpa using h
  constructor
  · constructor
    · exact ⟨_, hQ0.symm⟩
    · rintro y ⟨x₂, rfl⟩
      rw [hQ]
      have := hnonneg (x₂ + (A₂₂⁻¹ * A₂₁) *ᵥ x₁)
      linarith
  · exact hQ0
