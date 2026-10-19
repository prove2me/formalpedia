-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalMixedConjugateSelectedBranchCovariance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/8f92dfa5-681b-43a5-b18e-03acbebcd63a

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalMixedConjugateTargetCovariance
import Theorems.Thm_QuantumParallelRepetition_unconditionalMixedConjugateSelectedBranch_tensorAction
import Theorems.Thm_QuantumParallelRepetition_unconditionalMixedConjugateSelectedBranch_tensor_smul

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
namespace QuantumParallelRepetition
theorem _root_.solution
    {S N d L B m : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ]
    (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L)
    (positive : 0 < width (schedule j))
    (rest : EuclideanSpace ℂ τ) :
    Real.sqrt (width (schedule j) * (d : ℝ)) •
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
          width schedule ξ ζ j rest) =
      unconditionalMatchedVerifierTensor
        (unconditionalMixedConjugateAcceptedPhaseHarmonicTarget
          (N := N) (B := B) (width (schedule j)) m ξ)
        (unconditionalSelectedCopyRetainedWork
          (N := N) width schedule ξ ζ j rest) := by
  classical
  unfold unconditionalSelectedCopyIdealMatchedBranch
    unconditionalSelectedCopyIdealStage
  rw [unconditionalMixedConjugateSelectedBranch_tensorAction,
    unconditionalMixedConjugateSelectedBranch_tensor_smul]
  congr 1
  exact unconditionalMixedConjugateTargetCovariance
    positive grid dimension ξ ζ
end QuantumParallelRepetition
