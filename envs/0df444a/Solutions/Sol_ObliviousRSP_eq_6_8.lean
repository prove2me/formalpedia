-- Prove2me | solution 1 for ObliviousRSP.eq_6_8
-- status  : ACCEPTED   (prove)
-- author  : @Mceppaglia
-- created : 2026-11-20T12:46:27.58767+00:00
-- url     : https://prove2.me/submissions/5bdcaf9f-f73c-43e6-af90-f3c08df2ab87

import Mathlib
import Definitions.Def_ObliviousRSP_modifiedBobState

open scoped Kronecker
open ObliviousRSP

theorem solution {ι σ : Type} [Fintype ι] [Fintype σ] [DecidableEq σ]
    (Mm : Matrix (ι × σ) (ι × σ) ℂ) (φ : Matrix ι ι ℂ) :
    modifiedBobState Mm φ =
      ∑ j1 : σ, ∑ j2 : σ,
        ((Fintype.card σ : ℂ)⁻¹ * ((φ ⊗ₖ Matrix.single j1 j2 (1 : ℂ)) * Mm).trace) •
          Matrix.single j1 j2 (1 : ℂ) := by
  classical
  -- Summing scalar multiples of matrix units assembles their coefficient matrix.
  simp only [Matrix.smul_single, smul_eq_mul, mul_one, Matrix.sum_sum_single]
  ext a b
  -- Both traces reduce to the same double sum over specimen indices.
  simp [modifiedBobState, WildeQIT.partialTraceLeft, maxEnt, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.one_apply,
    Matrix.single_apply, Matrix.trace, Finset.mul_sum, mul_ite, ite_mul,
    ite_and, Finset.sum_ite_irrel]
  simp only [mul_left_comm, mul_assoc]
