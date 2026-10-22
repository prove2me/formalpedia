-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P41.symplectic_block_conditions
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:16:36.468706+00:00
-- url     : https://prove2.me/submissions/242eb139-c4df-419b-a2c7-ddf8d9832421

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41
noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

open QAlgorithms.Papers.Independent.Claimed50.P41

lemma g68k_sigma (n : ℕ) : sigma n = -Matrix.J (Fin n) ℝ := by
  simp [sigma, Matrix.J, Matrix.fromBlocks_neg]

lemma g68k_pres_iff {n : ℕ} (S : Matrix (Phase n) (Phase n) ℝ) :
    PreservesCanonicalForm S ↔ S ∈ Matrix.symplecticGroup (Fin n) ℝ := by
  rw [SymplecticGroup.mem_iff, PreservesCanonicalForm, g68k_sigma]
  simp [Matrix.mul_neg, Matrix.neg_mul]

lemma g68k_sigma_inv (n : ℕ) : (sigma n)⁻¹ = Matrix.J (Fin n) ℝ := by
  rw [g68k_sigma]
  apply Matrix.inv_eq_left_inv
  simp [Matrix.mul_neg, Matrix.J_squared]

lemma g68k_bracket {n : ℕ} (S : Matrix (Phase n) (Phase n) ℝ) (a b : Phase n) :
    linearCanonicalBracket S a b = (S * sigma n * S.transpose) a b := by
  simp only [linearCanonicalBracket, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]



/-- PDF p.11, (4.2): both equivalent sets of block conditions. -/
theorem solution (n : ℕ) (hn : 0 < n)
    (A B C D : Matrix (Fin n) (Fin n) ℝ) :
    (PreservesCanonicalForm (Matrix.fromBlocks A B C D) ↔
      (A * B.transpose).IsSymm ∧ (C * D.transpose).IsSymm ∧
        A * D.transpose - B * C.transpose = 1) ∧
    ((Matrix.fromBlocks A B C D).transpose * sigma n * Matrix.fromBlocks A B C D = sigma n ↔
      (A.transpose * C).IsSymm ∧ (B.transpose * D).IsSymm ∧
        A.transpose * D - C.transpose * B = 1) := by
  constructor
  · rw [g68k_pres_iff, ← SymplecticGroup.transpose_mem_iff, Matrix.fromBlocks_transpose,
      SymplecticGroup.fromBlocks_mem_iff]
    simp only [Matrix.transpose_transpose, Matrix.IsSymm, Matrix.transpose_mul]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1.symm, h2.symm, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1.symm, h2.symm, h3⟩
  · have : (Matrix.fromBlocks A B C D).transpose * sigma n * Matrix.fromBlocks A B C D = sigma n ↔
        Matrix.fromBlocks A B C D ∈ Matrix.symplecticGroup (Fin n) ℝ := by
      rw [SymplecticGroup.mem_iff', g68k_sigma]
      simp only [Matrix.mul_neg, Matrix.neg_mul, neg_inj]
    rw [this, SymplecticGroup.fromBlocks_mem_iff]
    simp only [Matrix.transpose_transpose, Matrix.IsSymm, Matrix.transpose_mul]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1.symm, h2.symm, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1.symm, h2.symm, h3⟩



end
