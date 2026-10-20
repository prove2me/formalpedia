-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P38.vectorization_partial_trace
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:36:49.261763+00:00
-- url     : https://prove2.me/submissions/f1823eee-c38f-4a39-8796-403799f43665

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P38

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P38

open scoped Matrix ComplexConjugate

/-- arXiv:2510.08154v1, PDF p.34, Appendix Fact 1, Eq.(125).
Definition 7 and Remark 11 fix the vectorization and its canonical swap.
The first tensor factor is traced without normalization. Dimensions may be
zero and M, A, B are arbitrary operators, without positivity or norm promises. -/
theorem solution (a b : ℕ)
    (M : Matrix (Fin b) (Fin a) ℂ)
    (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ) :
    traceLeft (pureDensity (vectorizeInputFirst M) * Matrix.kronecker A.transpose B) =
      M * A * Mᴴ * B := by
  ext y y'
  simp only [traceLeft, pureDensity, vectorizeInputFirst, Matrix.vec, Matrix.mul_apply,
    Matrix.of_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.transpose_apply,
    Fintype.sum_prod_type, Matrix.conjTranspose_apply, Finset.sum_mul,
    RCLike.star_def, PiLp.toLp_apply]
  conv_lhs => enter [2, i0]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, i0]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun p _ => ?_
  ring


end

