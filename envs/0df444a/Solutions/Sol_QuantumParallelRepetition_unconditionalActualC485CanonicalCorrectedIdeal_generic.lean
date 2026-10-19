-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualC485CanonicalCorrectedIdeal_generic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/d63f785d-6e66-438b-9111-759fe957c18c

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalMixedConjugateSelectedBranchCovariance
import Theorems.Thm_QuantumParallelRepetition_unconditionalPhaseCanonical_sourceScale_absorbed

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
    {S N d L B m : ℕ} {T : Type*}
    [Fintype T] [DecidableEq T]
    {width : Fin S → ℝ}
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L)
    (positive : 0 < width (schedule j))
    (grid : 0 < N) (dimension : 0 < d)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (width (schedule j) + 1))
    (rest : EuclideanSpace ℂ T) :
    unconditionalMatchedVerifierTensor
        (dSVDensityRationalPublicBucketCoherentPhaseSigmaState B
          (unconditionalConjugatePureVector
            (dSVDensityRationalCanonicalAcceptedUnitTarget
              positive grid fine ξ).val)
          (fun _ _ _ => embezzlementState (N * m)))
        ((‖dSVDensityRationalCanonicalAcceptedTarget
              (width (schedule j)) N ξ‖ /
            Real.sqrt (width (schedule j) * (d : ℝ))) •
          unconditionalSelectedCopyRetainedWork
            (N := N) width schedule ξ ζ j rest) =
      unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) B
          (conjugateUnitary
            (dSVDensityRationalCanonicalAliceBasis ξ)))
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) B
          (conjugateUnitary
            (dSVUniformDensityThresholdLeftBobBasis ζ)))
        (unconditionalSelectedCopyIdealMatchedBranch
          (N := N) (B := B) (m := m)
          width schedule ξ ζ j rest) := by
  have scale_positive : 0 < Real.sqrt (width (schedule j) * (d : ℝ)) := by
    positivity
  apply smul_right_injective _ scale_positive.ne'
  exact
    (unconditionalPhaseCanonical_sourceScale_absorbed
      (B := B) (m := N * m) positive grid dimension fine ξ
      (unconditionalSelectedCopyRetainedWork
        (N := N) width schedule ξ ζ j rest)).trans
      (unconditionalMixedConjugateSelectedBranchCovariance
        (B := B) (m := m) grid dimension width schedule ξ ζ j
        positive rest).symm
end QuantumParallelRepetition
