-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalClippedConjugateUnitTarget_distance_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/b023eacb-c63d-4946-bf66-2ad215c2d086

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalCanonicalAcceptedUnitTarget_distance_le
import Theorems.Thm_QuantumParallelRepetition_unconditionalConjugatePureVector_sub_norm

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
namespace QuantumParallelRepetition
theorem _root_.solution
    {d N : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (gamma : BipartiteUnitVector d)
    (psi : EuclideanSpace ℂ (Fin d × Fin d)) :
    ‖unconditionalConjugatePureVector psi -
      unconditionalConjugatePureVector
        (dSVDensityRationalCanonicalAcceptedUnitTarget
          width grid fine gamma).val‖ ^ 2 ≤
      2 * ‖psi - gamma.val‖ ^ 2 +
        8 * (1 / w + (d : ℝ) * w / (N : ℝ)) := by
  rw [unconditionalConjugatePureVector_sub_norm]
  let accepted : BipartiteUnitVector d :=
    dSVDensityRationalCanonicalAcceptedUnitTarget
      width grid fine gamma
  have triangle : ‖psi - accepted.val‖ ≤
      ‖psi - gamma.val‖ + ‖gamma.val - accepted.val‖ := by
    calc
      ‖psi - accepted.val‖ =
          ‖(psi - gamma.val) + (gamma.val - accepted.val)‖ := by
            congr 1
            abel
      _ ≤ _ := norm_add_le _ _
  have clipping :=
    dSVDensityRationalCanonicalAcceptedUnitTarget_distance_le
      width grid fine gamma
  have clipping_nonnegative :
      0 ≤ 1 / w + (d : ℝ) * w / (N : ℝ) := by
    positivity
  have clipping_squared :
      ‖gamma.val - accepted.val‖ ^ 2 ≤
        4 * (1 / w + (d : ℝ) * w / (N : ℝ)) := by
    change
      ‖gamma.val -
        (dSVDensityRationalCanonicalAcceptedUnitTarget
          width grid fine gamma).val‖ ^ 2 ≤ _
    nlinarith [
      norm_nonneg
        (gamma.val -
          (dSVDensityRationalCanonicalAcceptedUnitTarget
            width grid fine gamma).val),
      Real.sqrt_nonneg (1 / w + (d : ℝ) * w / (N : ℝ)),
      Real.sq_sqrt clipping_nonnegative]
  change ‖psi - accepted.val‖ ^ 2 ≤ _
  nlinarith [norm_nonneg (psi - accepted.val),
    norm_nonneg (psi - gamma.val),
    norm_nonneg (gamma.val - accepted.val),
    sq_nonneg (‖psi - gamma.val‖ - ‖gamma.val - accepted.val‖)]
end QuantumParallelRepetition
