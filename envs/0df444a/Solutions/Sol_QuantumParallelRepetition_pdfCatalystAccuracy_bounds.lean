-- Prove2me | solution 1 for QuantumParallelRepetition.pdfCatalystAccuracy_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/8c7a0b78-b56b-41b5-8552-56f332f38a9c

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
    {K ε : ℝ}
    (constant : 1 ≤ K) (gap : 0 < ε) (unit : ε ≤ 1) :
    0 < pdfCatalystAccuracy K ε ∧
      pdfCatalystAccuracy K ε ≤ 1 := by
  have denominator : 0 < 16 * K := by nlinarith
  have ratio : 0 < ε / (16 * K) := div_pos gap denominator
  have bounded : ε / (16 * K) ≤ 1 := by
    apply (div_le_iff₀ denominator).2
    nlinarith
  unfold pdfCatalystAccuracy
  exact ⟨pow_pos ratio 12, pow_le_one₀ ratio.le bounded⟩
end QuantumParallelRepetition
