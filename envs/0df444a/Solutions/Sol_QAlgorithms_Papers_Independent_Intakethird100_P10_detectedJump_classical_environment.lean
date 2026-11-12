-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P10.detectedJump_classical_environment
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T19:06:13.818284+00:00
-- url     : https://prove2.me/submissions/70104c73-8c7e-4317-930b-5ba028455a5c

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P10

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P58 (basisDensity)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Claimed50.P48 (indexedKrausDilation)

open QAlgorithms.Papers.Independent.Intakethird100.P10 in
theorem solution (gamma : ℝ) (hlo : 0 ≤ gamma) (hhi : gamma ≤ 1) :
    detectedJumpComplement gamma (basisDensity false) = basisDensity false ∧
    detectedJumpComplement gamma (basisDensity true) =
      ((1 - gamma : ℝ) : ℂ) • basisDensity false + (gamma : ℂ) • basisDensity true ∧
    Commute (detectedJumpComplement gamma (basisDensity false))
      (detectedJumpComplement gamma (basisDensity true)) := by
  have h1 : detectedJumpComplement gamma (basisDensity false) = basisDensity false := by
    ext a b
    cases a <;> cases b <;>
      simp [detectedJumpComplement, basisDensity, Matrix.trace, Fintype.sum_bool,
        Matrix.diagonal_apply]
  have h2 : detectedJumpComplement gamma (basisDensity true) =
      ((1 - gamma : ℝ) : ℂ) • basisDensity false + (gamma : ℂ) • basisDensity true := by
    ext a b
    cases a <;> cases b <;>
      simp [detectedJumpComplement, basisDensity, Matrix.trace, Fintype.sum_bool,
        Matrix.diagonal_apply]
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2]
  have hft : Commute (basisDensity false : Matrix Bool Bool ℂ) (basisDensity true) := by
    unfold Commute SemiconjBy
    ext a b
    cases a <;> cases b <;> simp [Matrix.mul_apply, basisDensity, Fintype.sum_bool]
  exact ((Commute.refl _).smul_right _).add_right (hft.smul_right _)
