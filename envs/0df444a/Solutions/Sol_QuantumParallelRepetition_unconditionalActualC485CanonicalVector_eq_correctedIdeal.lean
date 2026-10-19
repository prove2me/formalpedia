-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualC485CanonicalVector_eq_correctedIdeal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/74e505d7-de3e-457f-b4fe-53c0174f08c3

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualSelectedBranchLocalAction_decidableEq_irrel
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualC485CanonicalCorrectedIdeal_generic

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
    {S B N d L m : ℕ}
    {width : Fin S → ℝ}
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L)
    (positive : 0 < width (schedule j))
    (grid : 0 < N) (dimension : 0 < d)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (width (schedule j) + 1)) :
    integratorActualC485CanonicalVector
        (B := B) (m := m) schedule ξ ζ j positive grid fine =
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
          width schedule ξ ζ j
          (unconditionalActualCanonicalRetainedPhaseTail
            (S := S) (B := B) (N := N) (d := d) (L := L) j)) := by
  change
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
            (N := N) width schedule ξ ζ j
            (unconditionalActualCanonicalRetainedPhaseTail
              (S := S) (B := B) (N := N) (d := d) (L := L) j)) = _
  convert
    (unconditionalActualC485CanonicalCorrectedIdeal_generic
      (B := B) (m := m)
      schedule ξ ζ j positive grid dimension fine
      (unconditionalActualCanonicalRetainedPhaseTail
        (S := S) (B := B) (N := N) (d := d) (L := L) j)) using 1
  exact unconditionalActualSelectedBranchLocalAction_decidableEq_irrel
    _ _ _ _ _
end QuantumParallelRepetition
