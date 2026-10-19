-- Prove2me | solution 1 for QuantumParallelRepetition.pdfGapRate_le_half_conditioningTolerance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/a04014b8-6746-45b1-9d08-ebd853bea0eb

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_pdfGapRate_le_gap_div_eight

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
namespace QuantumParallelRepetition
theorem _root_.solution
    {B ε ell : ℝ}
    (constant : 1 ≤ B) (gap : 0 < ε)
    (unit : ε ≤ 1) (alphabet : 0 ≤ ell) :
    pdfGapRate B ε ell ≤
      pdfConditioningTolerance ε / 2 := by
  have exact_rate := pdfGapRate_le_gap_div_eight
    constant gap unit alphabet
  calc
    pdfGapRate B ε ell ≤ ε / 8 := exact_rate
    _ = pdfConditioningTolerance ε / 2 := by
      unfold pdfConditioningTolerance
      ring
end QuantumParallelRepetition
