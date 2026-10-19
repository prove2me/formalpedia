-- Prove2me | solution 1 for QuantumParallelRepetition.pdfGapBase_le_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/7a1c4b31-0d7b-44b1-a3f6-ead722067b79

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
    {B ε : ℝ}
    (constant : 1 ≤ B) (gap : 0 < ε) :
    0 < ε / (4 * B) ∧ ε / (4 * B) ≤ ε := by
  have denominator : 0 < 4 * B := by nlinarith
  constructor
  · exact div_pos gap denominator
  · apply (div_le_iff₀ denominator).2
    nlinarith
end QuantumParallelRepetition
