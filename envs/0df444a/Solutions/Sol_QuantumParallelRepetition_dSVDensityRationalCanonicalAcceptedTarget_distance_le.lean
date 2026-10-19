-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalCanonicalAcceptedTarget_distance_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/5bedd02d-bfb7-46d7-b89d-6dd0df8e0031

import Mathlib
import Definitions.Def_QuantumParallelRepetition

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
    (ξ : BipartiteUnitVector d) :
    ‖ξ.val - dSVDensityRationalCanonicalAcceptedTarget
        w N ξ‖ ≤
      Real.sqrt (1 / w + (d : ℝ) * w / (N : ℝ)) := by
  have nonnegative : 0 ≤ 1 / w + (d : ℝ) * w / (N : ℝ) := by
    positivity
  have squared :=
    dSVDensityRationalCanonicalAcceptedTarget_distance_sq_le
      width grid ξ
  have exact_sqrt := Real.sq_sqrt nonnegative
  nlinarith [norm_nonneg
    (ξ.val - dSVDensityRationalCanonicalAcceptedTarget w N ξ),
    Real.sqrt_nonneg (1 / w + (d : ℝ) * w / (N : ℝ))]
end QuantumParallelRepetition
