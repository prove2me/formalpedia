-- Prove2me | solution 1 for complex_posSemidef_eq_gram
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-07T21:38:10.288635+00:00
-- url     : https://prove2.me/submissions/e13a3926-5318-4f91-8fc6-ac271b129bb8

import Mathlib.Analysis.Matrix.Order
open scoped ComplexOrder MatrixOrder

theorem solution {idx : Type*} [Fintype idx] [DecidableEq idx]
    (M : Matrix idx idx Complex) (hM : M.PosSemidef) :
    ∃ A : Matrix idx idx Complex, M = Matrix.conjTranspose A * A := by
  obtain ⟨A, hA⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  refine ⟨A, ?_⟩
  simpa [Matrix.star_eq_conjTranspose] using hA