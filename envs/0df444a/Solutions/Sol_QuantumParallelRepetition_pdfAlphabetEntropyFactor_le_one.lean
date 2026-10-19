-- Prove2me | solution 1 for QuantumParallelRepetition.pdfAlphabetEntropyFactor_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/74e9ab44-4325-4a2c-ab80-a184dabecae8

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
    {ε ell : ℝ} (gap : 0 < ε) (alphabet : 0 ≤ ell) :
    (ε + 4 * ell) / (4 * (ε + ell)) ≤ 1 := by
  have denominator : 0 < 4 * (ε + ell) := by positivity
  apply (div_le_iff₀ denominator).2
  nlinarith
end QuantumParallelRepetition
