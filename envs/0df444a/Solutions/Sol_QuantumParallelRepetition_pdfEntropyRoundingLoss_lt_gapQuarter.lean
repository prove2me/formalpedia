-- Prove2me | solution 1 for QuantumParallelRepetition.pdfEntropyRoundingLoss_lt_gapQuarter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/40d41ef6-cead-4d89-a696-352a65a26f3b

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_pdfEntropyRoot_lt_gapBase

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
    B * η ^ (1 / 12 : ℝ) < ε / 4 := by
  have coefficient : 0 < B := by linarith
  calc
    B * η ^ (1 / 12 : ℝ) < B * (ε / (4 * B)) :=
      mul_lt_mul_of_pos_left
        (pdfEntropyRoot_lt_gapBase constant gap entropy small)
        coefficient
    _ = ε / 4 := by
      field_simp
end QuantumParallelRepetition
