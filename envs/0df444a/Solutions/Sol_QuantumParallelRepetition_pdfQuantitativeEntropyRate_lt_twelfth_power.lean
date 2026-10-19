-- Prove2me | solution 1 for QuantumParallelRepetition.pdfQuantitativeEntropyRate_lt_twelfth_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/eb82f018-1217-4719-9c93-be1926545699

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_pdfGapRate_pos
import Theorems.Thm_QuantumParallelRepetition_pdfConditioningTolerance_bounds
import Theorems.Thm_QuantumParallelRepetition_pdfGapRate_entropy_le_twelfth_power
import Theorems.Thm_QuantumParallelRepetition_pdfQuantitativeEntropyRate_lt

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
namespace QuantumParallelRepetition
theorem _root_.solution
    {B ε ell : ℝ} {n m k : ℕ} {t : ℝ}
    (constant : 1 ≤ B) (gap : 0 < ε)
    (unit : ε ≤ 1) (alphabet : 0 ≤ ell)
    (length : 0 < n)
    (remaining : (n : ℝ) / 2 < (m : ℝ))
    (postselection :
      t < pdfGapRate B ε ell * (n : ℝ))
    (conditioned :
      (k : ℝ) <
        pdfGapRate B ε ell * (n : ℝ) /
          pdfConditioningTolerance ε) :
    (t + (k : ℝ) * ell) / (m : ℝ) <
      (ε / (4 * B)) ^ 12 := by
  have Bpositive : 0 < B := lt_of_lt_of_le (by norm_num) constant
  have dpositive := pdfGapRate_pos Bpositive gap alphabet
  have taupositive : 0 < pdfConditioningTolerance ε :=
    (pdfConditioningTolerance_bounds gap unit).1
  have entropy := pdfQuantitativeEntropyRate_lt
    length dpositive taupositive alphabet remaining
    postselection conditioned
  have rewrite :
      2 * pdfGapRate B ε ell *
          (1 + ell / pdfConditioningTolerance ε) =
        2 * pdfGapRate B ε ell * (1 + 4 * ell / ε) := by
    unfold pdfConditioningTolerance
    have nonzero : ε ≠ 0 := ne_of_gt gap
    field_simp
  rw [rewrite] at entropy
  exact lt_of_lt_of_le entropy
    (pdfGapRate_entropy_le_twelfth_power
      constant gap alphabet)
end QuantumParallelRepetition
