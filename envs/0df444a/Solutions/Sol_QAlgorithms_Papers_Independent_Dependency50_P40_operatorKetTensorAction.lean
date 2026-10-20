-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P40.operatorKetTensorAction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:42:33.068037+00:00
-- url     : https://prove2.me/submissions/66b876cd-c614-47a5-b5e8-0213596dfcce

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P40

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P40

open QAlgorithms.Papers.Independent.Information100.P34 (dyad)

/-- PDF p.3, (11): the second tensor factor gives a transpose, not an adjoint. -/
theorem solution {h1 h2 k1 k2 : ℕ}
    (hh1 : 0 < h1) (hh2 : 0 < h2) (hk1 : 0 < k1) (hk2 : 0 < k2)
    (A : Matrix (Fin k1) (Fin h1) ℂ) (B : Matrix (Fin k2) (Fin h2) ℂ)
    (C : Matrix (Fin h1) (Fin h2) ℂ) :
    matrixAction (Matrix.kronecker A B) (operatorKet C) = operatorKet (A * C * Bᵀ) := by
  ext ⟨x, y⟩
  simp only [matrixAction, operatorKet, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_prod_type, Finset.sum_mul,
    PiLp.toLp_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

end
