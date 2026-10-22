-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P35.exchangeSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:50:06.770111+00:00
-- url     : https://prove2.me/submissions/2f12220a-036d-49fe-a903-d874702c578b

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35
noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50 QAlgorithms.Papers.Independent.Claimed50.P35

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39
  (displacementMatrix attenuatorMatrix amplifierMatrix thermalMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation conjugateKernel composeKernel partialRight isometryCoeff identityCoeff)

open QAlgorithms.Papers.Independent.Frontier30.P21 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

section G68ILIB

end G68ILIB

/-- V.A, (5.49), p.10: exact roots with multiplicities and nonnegative
occupation parameters. No doubling of the two g terms occurs. -/
theorem solution (N k Nc : ℝ)
    (hN : 0 ≤ N) (hk : 0 ≤ k) (hNc : 0 ≤ Nc) :
    (exchangeMatrix N k Nc).charpoly =
      (Polynomial.X - Polynomial.C (Complex.I *
        (((outputOccupation N k Nc - N + exchangeD N k Nc) / 2 : ℝ) : ℂ))) *
      (Polynomial.X - Polynomial.C (Complex.I *
        (((outputOccupation N k Nc - N - exchangeD N k Nc) / 2 : ℝ) : ℂ))) ∧
    0 ≤ (exchangeD N k Nc + outputOccupation N k Nc - N - 1) / 2 ∧
    0 ≤ (exchangeD N k Nc - outputOccupation N k Nc + N - 1) / 2 := by
  set M := outputOccupation N k Nc with hM
  set D := exchangeD N k Nc with hDdef
  have hMge : k ^ 2 * N ≤ M := by
    simp only [hM, outputOccupation, vacuumOutput]
    have := le_max_left 0 (k ^ 2 - 1)
    linarith
  have hMge2 : k ^ 2 - 1 + Nc + k ^ 2 * N ≤ M := by
    simp only [hM, outputOccupation, vacuumOutput]
    have := le_max_right 0 (k ^ 2 - 1)
    linarith
  have hk2 : 0 ≤ k ^ 2 * N := by positivity
  have hrad : 0 ≤ (N + M + 1) ^ 2 - 4 * k ^ 2 * N * (N + 1) := by
    nlinarith [sq_nonneg (N + 1 - k ^ 2 * N), mul_nonneg hN hk2]
  have hD2 : D ^ 2 = (N + M + 1) ^ 2 - 4 * k ^ 2 * N * (N + 1) := by
    simp only [hDdef, exchangeD]; rw [← hM, Real.sq_sqrt hrad]
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (N * (N + 1)) ^ 2 = N * (N + 1) := Real.sq_sqrt (by positivity)
  have hle : ∀ x : ℝ, x ^ 2 ≤ D ^ 2 → x ≤ D := by
    intro x hx
    nlinarith [sq_nonneg (x - D), sq_nonneg (x + D)]
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.charpoly_fin_two]
    have htr : (exchangeMatrix N k Nc).trace = Complex.I * (((M - N + D) / 2 : ℝ) : ℂ) +
        Complex.I * (((M - N - D) / 2 : ℝ) : ℂ) := by
      rw [Matrix.trace_fin_two]
      simp [exchangeMatrix, ← hM]
      push_cast
      ring
    have hdet : (exchangeMatrix N k Nc).det = Complex.I * (((M - N + D) / 2 : ℝ) : ℂ) *
        (Complex.I * (((M - N - D) / 2 : ℝ) : ℂ)) := by
      rw [Matrix.det_fin_two]
      simp [exchangeMatrix, ← hM]
      have hD2c : ((D : ℂ)) ^ 2 = ((N : ℂ) + M + 1) ^ 2 - 4 * (k : ℂ) ^ 2 * N * (N + 1) := by
        exact_mod_cast hD2
      have hs2c : ((Real.sqrt (N * (N + 1)) : ℝ) : ℂ) ^ 2 = (N : ℂ) * (N + 1) := by
        exact_mod_cast hs2
      push_cast
      linear_combination (-(((M : ℂ) + 1 / 2) * ((N : ℂ) + 1 / 2) +
        (((M : ℂ) - N) ^ 2 - (D : ℂ) ^ 2) / 4)) * Complex.I_sq - (k : ℂ) ^ 2 * hs2c
        - (1 / 4 : ℂ) * hD2c
    rw [htr, hdet]
    simp only [map_add, map_mul]
    ring
  · have : N + 1 - M ≤ D := by
      apply hle
      rw [hD2]
      nlinarith [mul_nonneg (show 0 ≤ N + 1 by linarith) (show 0 ≤ M - k ^ 2 * N by linarith)]
    linarith
  · have : M - N + 1 ≤ D := by
      apply hle
      rw [hD2]
      nlinarith [mul_nonneg hN (show 0 ≤ M + 1 - k ^ 2 * (N + 1) by linarith)]
    linarith



end
