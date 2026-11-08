-- Prove2me | solution 1 for ObliviousRSP.trace_mul_partialTraceRight
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:17:55.186252+00:00
-- url     : https://prove2.me/submissions/328e2b84-18a8-4324-b5a2-b4b01d397550

import Mathlib
import Definitions.Def_WildeQIT_partialTrace

open scoped Kronecker

theorem solution {a c : Type} [Fintype a] [Fintype c] [DecidableEq c]
    (A : Matrix a a ℂ) (B : Matrix (a × c) (a × c) ℂ) :
    (A * WildeQIT.partialTraceRight B).trace = ((A ⊗ₖ (1 : Matrix c c ℂ)) * B).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, WildeQIT.partialTraceRight,
    Matrix.of_apply, Matrix.kronecker_apply, Matrix.one_apply, Fintype.sum_prod_type, mul_ite,
    mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact Finset.sum_comm
