-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P41.symplectic_basic_identities
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:16:22.914783+00:00
-- url     : https://prove2.me/submissions/d517a35b-3a2f-46e7-8d06-0bd4399419a6

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



/-- PDF p.11, (4.1)(ii)–(iv): group identities and determinant +1. -/
theorem solution (n : ℕ) (hn : 0 < n)
    (S : Matrix (Phase n) (Phase n) ℝ) (hS : PreservesCanonicalForm S) :
    PreservesCanonicalForm (sigma n) ∧ PreservesCanonicalForm (-S) ∧ PreservesCanonicalForm S⁻¹ ∧
    PreservesCanonicalForm S.transpose ∧
    S.transpose = sigma n * S⁻¹ * (sigma n)⁻¹ ∧
    S⁻¹.transpose = sigma n * S * (sigma n)⁻¹ ∧
    S⁻¹ = sigma n * S.transpose * (sigma n)⁻¹ ∧ S.det = 1 := by
  rw [g68k_pres_iff] at hS
  simp only [g68k_pres_iff]
  have hinv := SymplecticGroup.inv_eq_symplectic_inv S hS
  have JJ := Matrix.J_squared (Fin n) ℝ
  have JT := Matrix.J_transpose (Fin n) ℝ
  refine ⟨?_, SymplecticGroup.neg_mem hS, ?_, SymplecticGroup.transpose_mem hS, ?_, ?_, ?_,
    SymplecticGroup.det_eq_one hS⟩
  · rw [g68k_sigma]; exact SymplecticGroup.neg_mem (SymplecticGroup.J_mem _ _)
  · have := (⟨S, hS⟩ : Matrix.symplecticGroup (Fin n) ℝ)⁻¹.2
    rwa [SymplecticGroup.coe_inv'] at this
  · rw [hinv, g68k_sigma_inv, g68k_sigma]
    simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc, JJ]
    rw [← Matrix.mul_assoc (Matrix.J _ _) (Matrix.J _ _), JJ]
    simp
  · rw [hinv, g68k_sigma_inv, g68k_sigma]
    simp [Matrix.transpose_mul, JT, Matrix.mul_assoc]
  · rw [hinv, g68k_sigma_inv, g68k_sigma]



end
