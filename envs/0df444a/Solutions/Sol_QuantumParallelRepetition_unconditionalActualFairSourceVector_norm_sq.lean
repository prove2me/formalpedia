-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairSourceVector_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/a6381d59-114f-458e-bae7-6ee0ad37ee0f

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalMatchedVerifierTensor_norm_sq
import Theorems.Thm_QuantumParallelRepetition_unconditionalConjugatePureVector_norm_sq
import Theorems.Thm_QuantumParallelRepetition_unconditionalSelectedCopy_coherentPhaseConstantWork_norm_sq

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
    (unit : ‖ψ‖ = 1) (j : Fin L) :
    ‖integratorActualC485SourceVector
        (S := S) (B := B) (N := N) (d := d) (L := L) (m := m)
        width schedule ξ ζ ψ j‖ ^ 2 =
      ‖integratorActualC485NormalizedDiagonalWork
          (S := S) (B := B) (N := N) (d := d) (L := L)
          width schedule ξ ζ j‖ ^ 2 := by
  unfold integratorActualC485SourceVector
  rw [unconditionalMatchedVerifierTensor_norm_sq,
    unconditionalSelectedCopy_coherentPhaseConstantWork_norm_sq
      phases,
    unconditionalConjugatePureVector_norm_sq,
    unit,
    embezzlementState_norm (N * m)
      (Nat.mul_pos grid harmonic)]
  ring
end QuantumParallelRepetition
