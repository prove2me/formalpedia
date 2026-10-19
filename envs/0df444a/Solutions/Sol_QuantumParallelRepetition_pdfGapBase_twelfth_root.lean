-- Prove2me | solution 1 for QuantumParallelRepetition.pdfGapBase_twelfth_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/9938042c-7495-4a4a-a955-25ecbd4549ac

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
    {B ε : ℝ} (constant : 1 ≤ B) (gap : 0 < ε) :
    ((ε / (4 * B)) ^ (12 : ℕ)) ^ (1 / 12 : ℝ) =
      ε / (4 * B) := by
  have base : 0 ≤ ε / (4 * B) :=
    (pdfGapBase_le_gap constant gap).1.le
  simpa [one_div] using
    (Real.pow_rpow_inv_natCast base (by norm_num : (12 : ℕ) ≠ 0))
end QuantumParallelRepetition
