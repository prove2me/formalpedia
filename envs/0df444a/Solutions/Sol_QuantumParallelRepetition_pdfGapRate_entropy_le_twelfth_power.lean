-- Prove2me | solution 1 for QuantumParallelRepetition.pdfGapRate_entropy_le_twelfth_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/c2439861-29d2-4f29-8f6c-c563c4e1fc36

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_pdfGapRate_entropy_factor
import Theorems.Thm_QuantumParallelRepetition_pdfAlphabetEntropyFactor_le_one

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
namespace QuantumParallelRepetition
theorem _root_.solution
    {B ε ell : ℝ}
    (constant : 1 ≤ B) (gap : 0 < ε) (alphabet : 0 ≤ ell) :
    2 * pdfGapRate B ε ell * (1 + 4 * ell / ε) ≤
      (ε / (4 * B)) ^ 12 := by
  have Bpositive : 0 < B := lt_of_lt_of_le (by norm_num) constant
  rw [pdfGapRate_entropy_factor Bpositive gap alphabet]
  have nonnegative : 0 ≤ (ε / (4 * B)) ^ 12 := by positivity
  calc
    (ε / (4 * B)) ^ 12 *
        ((ε + 4 * ell) / (4 * (ε + ell))) ≤
        (ε / (4 * B)) ^ 12 * 1 :=
          mul_le_mul_of_nonneg_left
            (pdfAlphabetEntropyFactor_le_one gap alphabet)
            nonnegative
    _ = _ := by ring
end QuantumParallelRepetition
