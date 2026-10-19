-- Prove2me | solution 1 for QuantumParallelRepetition.pdfEntropyRoot_lt_gapBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/34eca386-e1a9-4d06-a87d-12cf35a0ec75

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_pdfGapBase_twelfth_root

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
namespace QuantumParallelRepetition
theorem _root_.solution
    {B ε η : ℝ}
    (constant : 1 ≤ B) (gap : 0 < ε)
    (entropy : 0 ≤ η)
    (small : η < (ε / (4 * B)) ^ (12 : ℕ)) :
    η ^ (1 / 12 : ℝ) < ε / (4 * B) := by
  calc
    η ^ (1 / 12 : ℝ) <
        ((ε / (4 * B)) ^ (12 : ℕ)) ^ (1 / 12 : ℝ) :=
      Real.rpow_lt_rpow entropy small (by norm_num)
    _ = ε / (4 * B) :=
      pdfGapBase_twelfth_root constant gap
end QuantumParallelRepetition
