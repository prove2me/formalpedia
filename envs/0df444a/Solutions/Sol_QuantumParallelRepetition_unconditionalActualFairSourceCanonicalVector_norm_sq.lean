-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairSourceCanonicalVector_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/fb4064d8-b514-40c4-acfc-5f781821b24b

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairCanonicalVector_norm_sq
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceVector_norm_sq

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
        width schedule ξ ζ ψ j‖ ^ 2 =
      ‖integratorActualC485CanonicalVector
          (S := S) (B := B) (N := N) (d := d) (L := L) (m := m)
          (width := width) schedule ξ ζ j positive grid fine‖ ^ 2 := by
  rw [unconditionalActualFairSourceVector_norm_sq
    phases grid harmonic width schedule ξ ζ ψ unit j,
    unconditionalActualFairCanonicalVector_norm_sq
      phases grid harmonic width schedule ξ ζ j positive fine]
end QuantumParallelRepetition
