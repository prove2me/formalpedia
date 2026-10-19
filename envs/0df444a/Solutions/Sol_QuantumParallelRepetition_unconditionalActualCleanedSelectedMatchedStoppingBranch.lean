-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualCleanedSelectedMatchedStoppingBranch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/11d49e58-d811-4a0f-88d7-bfdd322846f9

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalSourcePhysicalStoppingBranch_sigmaContinuation
import Theorems.Thm_QuantumParallelRepetition_unconditionalSourcePhysicalCleanedStoppingFixedSource_physicalAction

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
namespace QuantumParallelRepetition
theorem _root_.solution
    {S B N d L m : ℕ} {R : Type}
    [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex S B ≃
        Fin B × R)
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L) :
    actualStoppingBranchVector
      (dSVUniformDensityPhysicalAsyncSigmaContinuation
        (unconditionalActualCleanedSelectedFiniteStageDecoder
          phaseSplit Q width schedule ξ
          (dSVUniformDensityAliceHistorySpectralCopy (N := N) ξ) A)
        (unconditionalActualCleanedSelectedFiniteStageDecoder
          phaseSplit Q width schedule ζ
          ((dSVUniformDensityBobHistoryCopyBasis (N := N) ζ)⁻¹) C)
        (actualStoppingQuestionLocalAction
          (unconditionalSourcePhysicalCleanedTargetFirstUnitary
            S B N d L m
            (dSVDensityRationalHeterogeneousTargetFirstSpectralAlice
              S B N d L m width schedule ξ))
          (unconditionalSourcePhysicalCleanedTargetFirstUnitary
            S B N d L m
            (dSVDensityRationalHeterogeneousTargetFirstSpectralBob
              S B N d L m width schedule ζ))
          (unconditionalSourcePhysicalCleanedStoppingFixedSource
            S B N d L m))) j.succ j.succ =
      toLp 2
        ((((unconditionalActualCleanedSelectedFullStageUnitary
              phaseSplit Q width schedule ξ
              (dSVUniformDensityAliceHistorySpectralCopy
                (N := N) ξ) A j :
            Matrix (UnconditionalSourcePhysicalStoppingPhaseFiber
              S B N d L m)
              (UnconditionalSourcePhysicalStoppingPhaseFiber
                S B N d L m) ℂ) ⊗ₖ
          (unconditionalActualCleanedSelectedFullStageUnitary
              phaseSplit Q width schedule ζ
              ((dSVUniformDensityBobHistoryCopyBasis
                (N := N) ζ)⁻¹) C j :
            Matrix (UnconditionalSourcePhysicalStoppingPhaseFiber
              S B N d L m)
              (UnconditionalSourcePhysicalStoppingPhaseFiber
                S B N d L m) ℂ)).mulVec
            (ofLp
              (actualStoppingBranchVector
                (unconditionalSourcePhysicalStoppingTargetFirstStateEquiv
                  S B N d L m
                  (dSVDensityRationalHeterogeneousOriginalStoppedState
                    S B N d L m width schedule ξ ζ))
                j.succ j.succ)))) := by
  rw [unconditionalSourcePhysicalCleanedStoppingFixedSource_physicalAction,
    unconditionalSourcePhysicalStoppingBranch_sigmaContinuation,
    unconditionalActualCleanedSelectedFiniteStageDecoder_succ,
    unconditionalActualCleanedSelectedFiniteStageDecoder_succ]
end QuantumParallelRepetition
