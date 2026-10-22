-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P41.linear_canonical_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:15:52.520516+00:00
-- url     : https://prove2.me/submissions/d73c68f0-2594-4315-bf49-cf8efb8a1ea0

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



/-- PDF pp.5–6, (2.3)–(2.6): preservation of all canonical PB/CCR coefficients
is exactly S beta S^T=beta; membership in Mathlib uses the opposite-sign J. -/
theorem solution (n : ℕ) (hn : 0 < n)
    (S : Matrix (Phase n) (Phase n) ℝ) :
    ((∀ a b, linearCanonicalBracket S a b = sigma n a b) ↔ PreservesCanonicalForm S) ∧
    (PreservesCanonicalForm S ↔ S ∈ Matrix.symplecticGroup (Fin n) ℝ) := by
  refine ⟨?_, g68k_pres_iff S⟩
  simp only [g68k_bracket, PreservesCanonicalForm]
  exact ⟨fun h => Matrix.ext h, fun h a b => by rw [h]⟩



end
