-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalCanonicalNormalizedTarget_distance_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/0251a72c-be32-4de5-9a01-94dd6db8ba97

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_dSVUniformDensity_normalize_sub_self_norm
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalCanonicalAcceptedTarget_distance_le

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
namespace QuantumParallelRepetition
theorem _root_.solution
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (ξ : BipartiteUnitVector d) :
    ‖ξ.val - dSVDensityRationalCanonicalNormalizedTarget
        w N ξ‖ ≤
      2 * Real.sqrt (1 / w + (d : ℝ) * w / (N : ℝ)) := by
  let v := dSVDensityRationalCanonicalAcceptedTarget w N ξ
  have nonzero : v ≠ 0 :=
    dSVDensityRationalCanonicalAcceptedTarget_ne_zero
      width grid fine ξ
  have reverse : |1 - ‖v‖| ≤ ‖ξ.val - v‖ := by
    have actual := abs_norm_sub_norm_le ξ.val v
    simpa [ξ.property] using actual
  have movement :
      ‖v - NormedSpace.normalize v‖ = |1 - ‖v‖| := by
    rw [norm_sub_rev]
    exact dSVUniformDensity_normalize_sub_self_norm v nonzero
  change ‖ξ.val - NormedSpace.normalize v‖ ≤ _
  calc
    ‖ξ.val - NormedSpace.normalize v‖ =
      ‖(ξ.val - v) + (v - NormedSpace.normalize v)‖ := by
        congr 1
        abel
    _ ≤ ‖ξ.val - v‖ + ‖v - NormedSpace.normalize v‖ :=
      norm_add_le _ _
    _ ≤ 2 * ‖ξ.val - v‖ := by
      rw [movement]
      linarith
    _ ≤ 2 * Real.sqrt (1 / w + (d : ℝ) * w / (N : ℝ)) := by
      gcongr
      exact dSVDensityRationalCanonicalAcceptedTarget_distance_le
        width grid ξ
end QuantumParallelRepetition
