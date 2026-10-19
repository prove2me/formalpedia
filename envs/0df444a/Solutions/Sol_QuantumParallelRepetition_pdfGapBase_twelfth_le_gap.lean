-- Prove2me | solution 1 for QuantumParallelRepetition.pdfGapBase_twelfth_le_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/8c00a294-c8f1-470f-90f4-8c4f2166459c

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_pdfGapBase_le_gap

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
namespace QuantumParallelRepetition
theorem _root_.solution
    {B ε : ℝ}
    (constant : 1 ≤ B) (gap : 0 < ε) (unit : ε ≤ 1) :
    (ε / (4 * B)) ^ 12 ≤ ε := by
  obtain ⟨nonnegative, bounded⟩ :=
    pdfGapBase_le_gap constant gap
  calc
    (ε / (4 * B)) ^ 12 ≤ ε ^ 12 :=
      pow_le_pow_left₀ nonnegative.le bounded 12
    _ = ε * ε ^ 11 := by ring
    _ ≤ ε * 1 :=
      mul_le_mul_of_nonneg_left
        (pow_le_one₀ gap.le unit) gap.le
    _ = ε := by ring
end QuantumParallelRepetition
