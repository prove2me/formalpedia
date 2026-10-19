-- Prove2me | solution 1 for QuantumParallelRepetition.pdfSqrtEight_le_twelfthRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/05876174-d592-41a2-b0a1-c872440dd255

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_pdfSqrt_le_twelfthRoot

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
namespace QuantumParallelRepetition
theorem _root_.solution
    {eta : ℝ} (nonnegative : 0 ≤ eta) (bounded : eta ≤ 1) :
    Real.sqrt (8 * eta) ≤
      Real.sqrt (8 : ℝ) * eta ^ (1 / 12 : ℝ) := by
  calc
    Real.sqrt (8 * eta) =
        Real.sqrt (8 : ℝ) * Real.sqrt eta := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
    _ ≤ Real.sqrt (8 : ℝ) * eta ^ (1 / 12 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (pdfSqrt_le_twelfthRoot nonnegative bounded)
        (Real.sqrt_nonneg _)
end QuantumParallelRepetition
