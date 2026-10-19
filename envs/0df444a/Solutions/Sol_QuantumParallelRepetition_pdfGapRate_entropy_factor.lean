-- Prove2me | solution 1 for QuantumParallelRepetition.pdfGapRate_entropy_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/6a6b9523-16ff-4f11-bf35-722432eabc02

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_pdfGapRate_eq_scaled_twelfth_power

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
namespace QuantumParallelRepetition
theorem _root_.solution
    {B ε ell : ℝ}
    (constant : 0 < B) (gap : 0 < ε) (alphabet : 0 ≤ ell) :
    2 * pdfGapRate B ε ell * (1 + 4 * ell / ε) =
      (ε / (4 * B)) ^ 12 *
        ((ε + 4 * ell) / (4 * (ε + ell))) := by
  have nonzero : B ≠ 0 := ne_of_gt constant
  have gap_nonzero : ε ≠ 0 := ne_of_gt gap
  have denominator : ε + ell ≠ 0 := ne_of_gt (by linarith)
  rw [pdfGapRate_eq_scaled_twelfth_power
    constant gap alphabet]
  field_simp
  ring
end QuantumParallelRepetition
