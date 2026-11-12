-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P10.amplitudeDamping_classical_environment
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T18:59:00.441093+00:00
-- url     : https://prove2.me/submissions/97b3ac3a-7c6a-4cf9-bcd1-1021c91ae810

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P10

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P58 (basisDensity)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Claimed50.P48 (indexedKrausDilation)

open QAlgorithms.Papers.Independent.Intakethird100.P10 in
theorem solution (gamma : ℝ) (hlo : 0 ≤ gamma) (hhi : gamma ≤ 1) :
    amplitudeComplement gamma (basisDensity false) = basisDensity false ∧
    amplitudeComplement gamma (basisDensity true) =
      ((1 - gamma : ℝ) : ℂ) • basisDensity false + (gamma : ℂ) • basisDensity true ∧
    Commute (amplitudeComplement gamma (basisDensity false))
      (amplitudeComplement gamma (basisDensity true)) := by
  have h1 : amplitudeComplement gamma (basisDensity false) = basisDensity false := by
    ext a b
    cases a <;> cases b <;> simp [amplitudeComplement, basisDensity]
  have h2 : amplitudeComplement gamma (basisDensity true) =
      ((1 - gamma : ℝ) : ℂ) • basisDensity false + (gamma : ℂ) • basisDensity true := by
    ext a b
    cases a <;> cases b <;> simp [amplitudeComplement, basisDensity]
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2]
  have hft : Commute (basisDensity false : Matrix Bool Bool ℂ) (basisDensity true) := by
    unfold Commute SemiconjBy
    ext a b
    cases a <;> cases b <;> simp [Matrix.mul_apply, basisDensity, Fintype.sum_bool]
  exact ((Commute.refl _).smul_right _).add_right (hft.smul_right _)
