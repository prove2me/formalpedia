-- Prove2me | solution 1 for QuantumParallelRepetition.pdfRoundingCoefficient_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/39ef12cc-adfd-4397-b21f-9f8624df3491

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_pdfRoundingCoefficient_two_le

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
    1 ≤ pdfRoundingCoefficient K := by
  have lower := pdfRoundingCoefficient_two_le constant
  linarith
end QuantumParallelRepetition
