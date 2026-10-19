-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairCanonicalVector_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/ad0bc9c9-0294-4452-8061-ac8fc6618388

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
    (ξ ζ : BipartiteUnitVector d) (j : Fin L)
    (positive : 0 < width (schedule j))
    (fine : (d : ℝ) / (N : ℝ) < 1 / (width (schedule j) + 1)) :
    ‖integratorActualC485CanonicalVector
        (B := B) (m := m) schedule ξ ζ j positive grid fine‖ ^ 2 =
      ‖integratorActualC485NormalizedDiagonalWork
          (B := B) (N := N) width schedule ξ ζ j‖ ^ 2 := by
  unfold integratorActualC485CanonicalVector
  rw [unconditionalMatchedVerifierTensor_norm_sq,
    unconditionalSelectedCopy_coherentPhaseConstantWork_norm_sq
      phases,
    unconditionalConjugatePureVector_norm_sq,
    (dSVDensityRationalCanonicalAcceptedUnitTarget
      positive grid fine ξ).property,
    embezzlementState_norm (N * m)
      (Nat.mul_pos grid harmonic)]
  ring
end QuantumParallelRepetition
