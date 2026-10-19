-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalSelectedCopy_conjugateAcceptedTarget_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/6dbeeb50-ca19-4cfe-8abe-cf1e6cee2362

import Mathlib
import Definitions.Def_QuantumParallelRepetition
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
namespace QuantumParallelRepetition
theorem _root_.solution
    {d N B m : ℕ} (phases : 0 < B)
    (grid : 0 < N) (harmonic : 0 < m)
    (w : ℝ) (ξ : BipartiteUnitVector d) :
    ‖unconditionalMixedConjugateAcceptedPhaseHarmonicTarget
        (N := N) (B := B) w m ξ‖ ^ 2 =
      ‖dSVDensityRationalCanonicalAcceptedTarget w N ξ‖ ^ 2 := by
  unfold unconditionalMixedConjugateAcceptedPhaseHarmonicTarget
  rw [unconditionalSelectedCopy_coherentPhaseConstantWork_norm_sq
    phases]
  rw [unconditionalConjugatePureVector_norm_sq,
    embezzlementState_norm (N * m) (Nat.mul_pos grid harmonic)]
  ring
end QuantumParallelRepetition
