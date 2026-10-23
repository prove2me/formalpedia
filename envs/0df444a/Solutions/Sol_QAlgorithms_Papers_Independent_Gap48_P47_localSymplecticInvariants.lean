-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P47.localSymplecticInvariants
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T14:06:31.894338+00:00
-- url     : https://prove2.me/submissions/45640997-4ad5-4551-8b5a-ba01cf355f63

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P47

noncomputable section

open scoped BigOperators ComplexOrder

namespace QAlgorithms.Papers.Independent.Gap48.P47

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov FockIndex DensityKernel GaussianWithCovariance CharacteristicSummable
   multimodeWeylTrace covarianceCharacteristicValue modeCovarianceBlock
   standardFormCovariance)

open QAlgorithms.Papers.Independent.Renew46.P39 (AffineMultimodeGaussianUnitary)

open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P14 (boundedUnitaryConjugation)

attribute [local instance] Classical.propDecidable Classical.decEq

open Matrix

def x8s (S : Cov 1) : Matrix (Fin 2) (Fin 2) ℝ := fun a b => S (0, a) (0, b)

theorem x8_det_one (S : Cov 1)
    (h : S.transpose * interleavedSymplecticForm 1 * S = interleavedSymplecticForm 1) :
    (x8s S).det = 1 := by
  have := congrFun (congrFun h (0, 0)) (0, 1)
  simp [mul_apply, interleavedSymplecticForm, Fintype.sum_prod_type, Fin.sum_univ_two] at this
  rw [det_fin_two]
  simp only [x8s]
  linarith

theorem x8_block (G : Cov 2) (S1 S2 : Cov 1) (i j : Fin 2) :
    modeCovarianceBlock (localCongruence G S1 S2) i j =
      (![x8s S1, x8s S2] i)ᵀ * modeCovarianceBlock G i j * ![x8s S1, x8s S2] j := by
  ext a b
  fin_cases i <;> fin_cases j <;>
  simp [modeCovarianceBlock, localCongruence, localSymplecticMatrix, mul_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, x8s] <;> ring

theorem x8_S (S1 S2 : Cov 1) : localSymplecticMatrix S1 S2 =
    (blockDiagonal ![x8s S1, x8s S2]).submatrix Prod.swap Prod.swap := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases j <;> simp [localSymplecticMatrix, blockDiagonal_apply, x8s]

theorem x8_main (rho : TwoModeGaussianDensity) (S1 S2 : Cov 1)
    (hS1 : S1.transpose * interleavedSymplecticForm 1 * S1 =
      interleavedSymplecticForm 1)
    (hS2 : S2.transpose * interleavedSymplecticForm 1 * S2 =
      interleavedSymplecticForm 1) :
    let changed := localCongruence rho.covariance S1 S2
    (modeCovarianceBlock changed 0 0).det =
      (modeCovarianceBlock rho.covariance 0 0).det ∧
    (modeCovarianceBlock changed 1 1).det =
      (modeCovarianceBlock rho.covariance 1 1).det ∧
    (modeCovarianceBlock changed 0 1).det =
      (modeCovarianceBlock rho.covariance 0 1).det ∧
    changed.det = rho.covariance.det := by
  intro changed
  have h1 := x8_det_one S1 hS1
  have h2 := x8_det_one S2 hS2
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (modeCovarianceBlock (localCongruence rho.covariance S1 S2) 0 0).det = _
    rw [x8_block]; simp [det_mul, det_transpose, h1]
  · show (modeCovarianceBlock (localCongruence rho.covariance S1 S2) 1 1).det = _
    rw [x8_block]; simp [det_mul, det_transpose, h2]
  · show (modeCovarianceBlock (localCongruence rho.covariance S1 S2) 0 1).det = _
    rw [x8_block]; simp [det_mul, det_transpose, h1, h2]
  · show (localCongruence rho.covariance S1 S2).det = _
    have hS : (localSymplecticMatrix S1 S2).det = 1 := by
      rw [x8_S]
      have : ((blockDiagonal ![x8s S1, x8s S2]).submatrix Prod.swap Prod.swap).det =
          ((blockDiagonal ![x8s S1, x8s S2]).submatrix (Equiv.prodComm _ _)
            (Equiv.prodComm _ _)).det := rfl
      rw [this, det_submatrix_equiv_self, det_blockDiagonal, Fin.prod_univ_two]
      simp [h1, h2]
    unfold localCongruence
    simp only
    rw [det_mul, det_mul, det_transpose, hS]; ring

end QAlgorithms.Papers.Independent.Gap48.P47

open QAlgorithms.Papers.Independent.Gap48.P47 QAlgorithms.Papers.Independent.Claimed50.P19
  QAlgorithms.Papers.Independent.Frontier30.P08 in
theorem solution (rho : TwoModeGaussianDensity) (S1 S2 : Cov 1)
    (hS1 : S1.transpose * interleavedSymplecticForm 1 * S1 =
      interleavedSymplecticForm 1)
    (hS2 : S2.transpose * interleavedSymplecticForm 1 * S2 =
      interleavedSymplecticForm 1) :
    let changed := localCongruence rho.covariance S1 S2
    (modeCovarianceBlock changed 0 0).det =
      (modeCovarianceBlock rho.covariance 0 0).det ∧
    (modeCovarianceBlock changed 1 1).det =
      (modeCovarianceBlock rho.covariance 1 1).det ∧
    (modeCovarianceBlock changed 0 1).det =
      (modeCovarianceBlock rho.covariance 0 1).det ∧
    changed.det = rho.covariance.det :=
  x8_main rho S1 S2 hS1 hS2
