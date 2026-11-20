-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P39.triangular_symplectic_criterion
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T12:11:14.676024+00:00
-- url     : https://prove2.me/submissions/61bfc5f6-494e-4634-96ff-a8b0cc3aa0f1

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P39
noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Intake100.P39

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic canonicalJ)

open QAlgorithms.Papers.Independent.Gap50repair.P01
  (Coord GroupedRealMatrix omegaMatrix omegaR omegaC shifted generalizedSpace
    IsEigenvalue HasNilpotentHeight restrictedKernel GeneralizedQuotient)

theorem _root_.solution {n : ℕ}
    (B C D : Matrix (Fin n) (Fin n) ℝ) :
    IsSymplectic (Matrix.fromBlocks B C 0 D) ↔
      IsUnit D.det ∧ B = D.transpose⁻¹ ∧
        ∃ S : Matrix (Fin n) (Fin n) ℝ, S.transpose = S ∧ C = D.transpose⁻¹ * S := by
  unfold IsSymplectic canonicalJ
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_inj]
  simp only [Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_one, add_zero, zero_add, Matrix.zero_mul, true_and]
  rw [neg_inj, ← sub_eq_add_neg, sub_eq_zero]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hDt : IsUnit Dᵀ.det := Matrix.isUnit_det_of_right_inverse h2
    refine ⟨by rwa [Matrix.det_transpose] at hDt, (Matrix.inv_eq_right_inv h2).symm, Dᵀ * C, ?_, ?_⟩
    · rw [Matrix.transpose_mul, Matrix.transpose_transpose, h3]
    · rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hDt, Matrix.one_mul]
  · rintro ⟨hd, rfl, S, hS, rfl⟩
    have hDt : IsUnit Dᵀ.det := by rwa [Matrix.det_transpose]
    have e1 : (Dᵀ⁻¹)ᵀ * D = 1 := by
      rw [Matrix.transpose_nonsing_inv, Matrix.transpose_transpose, Matrix.nonsing_inv_mul _ hd]
    refine ⟨e1, Matrix.mul_nonsing_inv _ hDt, ?_⟩
    rw [Matrix.transpose_mul, hS, Matrix.mul_assoc, e1, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hDt, Matrix.one_mul]

end QAlgorithms.Papers.Independent.Intake100.P39

end
