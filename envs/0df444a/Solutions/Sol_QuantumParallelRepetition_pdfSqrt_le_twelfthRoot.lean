-- Prove2me | solution 1 for QuantumParallelRepetition.pdfSqrt_le_twelfthRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/684279bb-3cad-4c30-82f7-773b860880b4

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
namespace QuantumParallelRepetition
theorem _root_.solution
    {eta : ℝ} (nonnegative : 0 ≤ eta) (bounded : eta ≤ 1) :
    Real.sqrt eta ≤ eta ^ (1 / 12 : ℝ) := by
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_ge'
    nonnegative bounded (by norm_num) (by norm_num)
end QuantumParallelRepetition
