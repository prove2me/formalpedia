-- Prove2me | solution 1 for QuantumParallelRepetition.pdfRoundingCoefficient_two_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/128dc52f-bb3d-472b-a9cb-70de1711d626

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_pdfUniversalErrorCeiling_pos

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
namespace QuantumParallelRepetition
theorem _root_.solution
    {K : ℝ} (constant : 1 ≤ K) :
    2 ≤ pdfRoundingCoefficient K := by
  have nonnegative : 0 ≤ K := by linarith
  have ceiling_nonnegative : 0 ≤ universalErrorCeiling K :=
    (pdfUniversalErrorCeiling_pos constant).le
  have first_nonnegative :
      0 ≤ (5 + 2 * universalErrorCeiling K) *
        Real.sqrt (3 / 2 : ℝ) := by positivity
  have quantum_nonnegative :
      0 ≤ 2 * K * (32 : ℝ) ^ (1 / 12 : ℝ) := by positivity
  have eight : 1 ≤ Real.sqrt (8 : ℝ) :=
    Real.one_le_sqrt.mpr (by norm_num)
  unfold pdfRoundingCoefficient
  nlinarith
end QuantumParallelRepetition
