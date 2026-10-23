-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap50repair.P01.complex_linearity_blocks
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:32:04.392759+00:00
-- url     : https://prove2.me/submissions/5e4771c5-d646-4c46-967c-6e7e2bd985ed

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01
noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Gap50repair.P01
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

section
attribute [local instance] Classical.propDecidable

theorem solution {n : ℕ} (F B C D : Matrix (Fin n) (Fin n) ℝ) :
    (CommutesWithComplexStructure (Matrix.fromBlocks F B C D) ↔ D = F ∧ C = -B) ∧
    (D = F → C = -B → ∀ x y : Fin n → ℝ,
      (fun i => (((Matrix.fromBlocks F B C D).mulVec (Sum.elim x y)) (Sum.inl i) : ℂ) +
        Complex.I*(((Matrix.fromBlocks F B C D).mulVec (Sum.elim x y)) (Sum.inr i) : ℂ)) =
      (complexActionMatrix (Matrix.fromBlocks F B C D)).mulVec (fun i => (x i : ℂ)+Complex.I*(y i : ℂ))) := by
  refine ⟨?_, ?_⟩
  · unfold CommutesWithComplexStructure jMatrix omegaMatrix
    rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
    simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, Matrix.zero_mul, Matrix.one_mul,
      Matrix.neg_mul, zero_add, add_zero]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h2.symm, by rw [← h1]⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨by simp, rfl, rfl, by simp⟩
  · rintro rfl rfl x y
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.fromBlocks_apply₁₁, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Sum.elim_inl, Sum.elim_inr, complexActionMatrix, Matrix.neg_apply]
    push_cast
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring_nf
    rw [Complex.I_sq]
    ring

end
