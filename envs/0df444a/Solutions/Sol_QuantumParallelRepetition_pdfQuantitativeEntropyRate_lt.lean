-- Prove2me | solution 1 for QuantumParallelRepetition.pdfQuantitativeEntropyRate_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/1908ac75-2d6f-4c3e-bbf6-d09c6e56b4ef

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
    {n m k : ℕ} {t d τ ell : ℝ}
    (length : 0 < n) (rate : 0 < d) (tolerance : 0 < τ)
    (alphabet : 0 ≤ ell)
    (remaining : (n : ℝ) / 2 < (m : ℝ))
    (postselection : t < d * (n : ℝ))
    (conditioned : (k : ℝ) < d * (n : ℝ) / τ) :
    (t + (k : ℝ) * ell) / (m : ℝ) <
      2 * d * (1 + ell / τ) := by
  have length_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast length
  have mpositive : (0 : ℝ) < (m : ℝ) := by nlinarith
  have ratio_nonnegative : 0 ≤ ell / τ :=
    div_nonneg alphabet tolerance.le
  have factor : 0 < d * (1 + ell / τ) := by
    exact mul_pos rate (by linarith)
  have alphabet_bound :
      (k : ℝ) * ell ≤ (d * (n : ℝ) / τ) * ell :=
    mul_le_mul_of_nonneg_right (le_of_lt conditioned) alphabet
  have numerator :
      t + (k : ℝ) * ell < d * (n : ℝ) * (1 + ell / τ) := by
    calc
      t + (k : ℝ) * ell <
          d * (n : ℝ) + (d * (n : ℝ) / τ) * ell :=
        add_lt_add_of_lt_of_le postselection alphabet_bound
      _ = d * (n : ℝ) * (1 + ell / τ) := by ring
  apply (div_lt_iff₀ mpositive).2
  have horizon : (n : ℝ) < 2 * (m : ℝ) := by nlinarith
  have scaled := mul_lt_mul_of_pos_left horizon factor
  nlinarith
end QuantumParallelRepetition
