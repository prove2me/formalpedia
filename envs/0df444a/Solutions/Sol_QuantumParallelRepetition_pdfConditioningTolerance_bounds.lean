-- Prove2me | solution 1 for QuantumParallelRepetition.pdfConditioningTolerance_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/9e747d9a-7927-406e-9b9b-5db5f5142e5a

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
    {ε : ℝ} (gap : 0 < ε) (unit : ε ≤ 1) :
    0 < pdfConditioningTolerance ε ∧
      pdfConditioningTolerance ε ≤ 1 / 4 := by
  unfold pdfConditioningTolerance
  constructor <;> nlinarith
end QuantumParallelRepetition
