-- Prove2me | solution 1 for QuantumParallelRepetition.pdfCatalystAccuracy_samplingLoss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/c5e130c2-7166-48cb-a7e7-22f4134fcc4e

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_pdfCatalystAccuracy_twelfth_root

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
namespace QuantumParallelRepetition
theorem _root_.solution
    {K ε : ℝ} (constant : 1 ≤ K) (gap : 0 < ε) :
    2 * K * (pdfCatalystAccuracy K ε) ^ (1 / 12 : ℝ) =
      ε / 8 := by
  have coefficient : 0 < K := by linarith
  rw [pdfCatalystAccuracy_twelfth_root constant gap]
  field_simp
  norm_num
end QuantumParallelRepetition
