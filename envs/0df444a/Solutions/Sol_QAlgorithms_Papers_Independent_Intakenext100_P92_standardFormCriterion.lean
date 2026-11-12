-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P92.standardFormCriterion
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T01:53:38.232879+00:00
-- url     : https://prove2.me/submissions/b8ed86c1-4f62-4ca3-99e5-1892ee8b22ac

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P92

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder

open QAlgorithms.Papers.Independent.Advance50.P48
  (TwoKernel GaussianTwo IsDiscordCovariance characteristicTwo
   covarianceModeBlock totalPhotonEnergy)

open QAlgorithms.Papers.Independent.Frontier30.P04 (modePhase Covariance twoModeStandard)

open QAlgorithms.Papers.Independent.Claimed50.P30 (canonicalOmega)

attribute [local instance] Classical.propDecidable Classical.decEq

set_option maxHeartbeats 1600000 in
open QAlgorithms.Papers.Independent.Intakenext100.P92 in
theorem solution (a b c1 c2 : ℝ) :
    SimonCriterion (twoModeStandard a b c1 c2) ↔
      a ^ 2 + b ^ 2 + 2 * |c1 * c2| - 1 / 4 ≤
        4 * (a * b - c1 ^ 2) * (a * b - c2 ^ 2) := by
  have hdet : ∀ M : Matrix (Fin 1 × Fin 2) (Fin 1 × Fin 2) ℝ,
      M.det = M (0, 0) (0, 0) * M (0, 1) (0, 1) - M (0, 0) (0, 1) * M (0, 1) (0, 0) := by
    intro M
    rw [← Matrix.det_reindex_self (Equiv.uniqueProd (Fin 2) (Fin 1)) M, Matrix.det_fin_two]
    simp [Matrix.reindex_apply, Matrix.submatrix_apply]
  have hI0 : simonInvariant (twoModeStandard a b c1 c2) 0 = a ^ 2 := by
    have h : simonInvariant (twoModeStandard a b c1 c2) 0 =
        (covarianceModeBlock (twoModeStandard a b c1 c2) 0 0).det := by
      simp [simonInvariant]
    rw [h, hdet]
    simp [covarianceModeBlock, twoModeStandard] <;> ring
  have hI1 : simonInvariant (twoModeStandard a b c1 c2) 1 = b ^ 2 := by
    have h : simonInvariant (twoModeStandard a b c1 c2) 1 =
        (covarianceModeBlock (twoModeStandard a b c1 c2) 1 1).det := by
      simp [simonInvariant]
    rw [h, hdet]
    simp [covarianceModeBlock, twoModeStandard] <;> ring
  have hI2 : simonInvariant (twoModeStandard a b c1 c2) 2 = c1 * c2 := by
    have h : simonInvariant (twoModeStandard a b c1 c2) 2 =
        (covarianceModeBlock (twoModeStandard a b c1 c2) 0 1).det := by
      simp [simonInvariant]
    rw [h, hdet]
    simp [covarianceModeBlock, twoModeStandard]
  have hI3 : simonInvariant (twoModeStandard a b c1 c2) 3 = a * b * (c1 ^ 2 + c2 ^ 2) := by
    simp [simonInvariant, covarianceModeBlock, twoModeStandard, canonicalOmega, Matrix.trace,
      Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.transpose_apply] <;> ring
  unfold SimonCriterion
  rw [hI0, hI1, hI2, hI3]
  have habs : |c1 * c2| ^ 2 = (c1 * c2) ^ 2 := sq_abs _
  constructor
  · intro h
    nlinarith [habs]
  · intro h
    nlinarith [habs]

end
