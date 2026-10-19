-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalCanonicalAcceptedUnitTarget_distance_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/e9dbe5d2-f79d-410a-ad09-1ee3f8bac905

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalCanonicalNormalizedTarget_distance_le

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
    ‖ξ.val -
        (dSVDensityRationalCanonicalAcceptedUnitTarget
          width grid fine ξ).val‖ ≤
      2 * Real.sqrt (1 / w + (d : ℝ) * w / (N : ℝ)) :=
  dSVDensityRationalCanonicalNormalizedTarget_distance_le
    width grid fine ξ
end QuantumParallelRepetition
