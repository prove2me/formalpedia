-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairSourceCanonicalVector_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/c87c911c-8442-462c-afcb-458d6ba74c70

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceCanonicalVector_norm_sq

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] Classical.propDecidable
namespace QuantumParallelRepetition
theorem _root_.solution
    {S B N d L m : ℕ}
    (phases : 0 < B) (grid : 0 < N) (harmonic : 0 < m)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (ψ : EuclideanSpace ℂ (Fin d × Fin d))
    (unit : ‖ψ‖ = 1) (j : Fin L)
    (positive : 0 < width (schedule j))
    (fine : (d : ℝ) / (N : ℝ) < 1 / (width (schedule j) + 1)) :
    ‖integratorActualC485SourceVector
        (S := S) (B := B) (N := N) (d := d) (L := L) (m := m)
        width schedule ξ ζ ψ j‖ =
      ‖integratorActualC485CanonicalVector
          (S := S) (B := B) (N := N) (d := d) (L := L) (m := m)
          (width := width) schedule ξ ζ j positive grid fine‖ := by
  have squared :=
    unconditionalActualFairSourceCanonicalVector_norm_sq
      phases grid harmonic width schedule ξ ζ ψ unit j positive fine
  nlinarith [
    norm_nonneg (integratorActualC485SourceVector
      (S := S) (B := B) (N := N) (d := d) (L := L) (m := m)
      width schedule ξ ζ ψ j),
    norm_nonneg (integratorActualC485CanonicalVector
      (S := S) (B := B) (N := N) (d := d) (L := L) (m := m)
      (width := width) schedule ξ ζ j positive grid fine)]
end QuantumParallelRepetition
