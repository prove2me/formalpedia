-- Prove2me | solution 1 for QuantumParallelRepetition.pdfGapRate_le_gap_div_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/6bbc9d38-8241-4ebb-b890-283a12ff7643

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_pdfGapRate_eq_scaled_twelfth_power
import Theorems.Thm_QuantumParallelRepetition_pdfGapBase_twelfth_le_gap

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
    pdfGapRate B ε ell ≤ ε / 8 := by
  have Bpositive : 0 < B := lt_of_lt_of_le (by norm_num) constant
  have denominator : 0 < ε + ell := by linarith
  have fraction : ε / (ε + ell) ≤ 1 := by
    apply (div_le_iff₀ denominator).2
    linarith
  have root := pdfGapBase_twelfth_le_gap constant gap unit
  rw [pdfGapRate_eq_scaled_twelfth_power
    Bpositive gap alphabet]
  have nonnegative : 0 ≤ (ε / (4 * B)) ^ 12 := by positivity
  calc
    ε / (8 * (ε + ell)) * (ε / (4 * B)) ^ 12 =
        (ε / (ε + ell)) * (ε / (4 * B)) ^ 12 / 8 := by
          field_simp [ne_of_gt denominator, ne_of_gt Bpositive]
    _ ≤ 1 * ε / 8 := by
          gcongr
    _ = ε / 8 := by ring
end QuantumParallelRepetition
