-- Prove2me | solution 1 for QuantumParallelRepetition.pdfPinskerRoot_le_twelfthRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/d154dc54-13ad-41f6-aa81-17e457c5a850

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
    {eta kappa : ℝ}
    (nonnegative : 0 ≤ eta)
    (bounded : eta ≤ 1)
    (pinsker : kappa ≤ Real.sqrt ((3 / 2 : ℝ) * eta)) :
    kappa ≤ Real.sqrt (3 / 2 : ℝ) * eta ^ (1 / 12 : ℝ) := by
  calc
    kappa ≤ Real.sqrt ((3 / 2 : ℝ) * eta) := pinsker
    _ = Real.sqrt (3 / 2 : ℝ) * Real.sqrt eta := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3 / 2)]
    _ ≤ Real.sqrt (3 / 2 : ℝ) * eta ^ (1 / 12 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (pdfSqrt_le_twelfthRoot nonnegative bounded)
        (Real.sqrt_nonneg _)
end QuantumParallelRepetition
