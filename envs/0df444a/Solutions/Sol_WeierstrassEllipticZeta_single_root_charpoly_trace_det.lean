-- Prove2me | solution 1 for WeierstrassEllipticZeta.single_root_charpoly_trace_det
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-12T01:23:08.416081+00:00
-- url     : https://prove2.me/submissions/2f449d75-4438-4153-9784-1df16bd8d0a7

import Mathlib.Algebra.Polynomial.Monic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Trace



open Polynomial

theorem solution
    (K M : Type*) [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (f : Module.End K M) (z : K) (d : ℕ)
    (h : f.charpoly = (X - C z) ^ d) :
    LinearMap.trace K M f = (d : K) * z ∧ f.det = z ^ d := by
  classical
  let b := Module.Free.chooseBasis K M
  have hd : Module.finrank K M = d := by
    rw [← f.charpoly_natDegree, h]
    simp
  constructor
  · rw [LinearMap.trace_eq_matrix_trace K b, Matrix.trace_eq_neg_charpoly_nextCoeff,
      LinearMap.charpoly_toMatrix, h, (monic_X_sub_C z).nextCoeff_pow, nextCoeff_X_sub_C]
    simp [nsmul_eq_mul]
  · rw [← LinearMap.det_toMatrix b, Matrix.det_eq_sign_charpoly_coeff,
      ← Module.finrank_eq_card_chooseBasisIndex, LinearMap.charpoly_toMatrix, h, hd,
      coeff_zero_eq_eval_zero]
    simp only [eval_pow, eval_sub, eval_X, eval_C, zero_sub]
    rw [← mul_pow]
    simp

