-- Prove2me | solution 1 for QuantumParallelRepetition.pdfCatalystAccuracy_twelfth_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/4b6d9dd6-6ea5-4481-bcbb-dd02ecd1ef64

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
    {K ε : ℝ} (constant : 1 ≤ K) (gap : 0 < ε) :
    (pdfCatalystAccuracy K ε) ^ (1 / 12 : ℝ) =
      ε / (16 * K) := by
  have denominator : 0 < 16 * K := by nlinarith
  have base : 0 ≤ ε / (16 * K) := (div_pos gap denominator).le
  unfold pdfCatalystAccuracy
  simpa [one_div] using
    (Real.pow_rpow_inv_natCast base (by norm_num : (12 : ℕ) ≠ 0))
end QuantumParallelRepetition
