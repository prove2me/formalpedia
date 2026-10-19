-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFixedSourceFullPhysicalBilateralStageTransport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/669c9f94-572d-47d2-b985-1461186e41db

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalRegroupedSelectedRetainedReindexAction
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualFixedSourceFullBilateralRegroup_eq

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
    (Q : ℕ) (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (spectralA spectralB : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ)
    (A C : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L)
    (z : EuclideanSpace ℂ
      (UnconditionalSourcePhysicalStoppingPhaseFiber
          S B N d L m ×
       UnconditionalSourcePhysicalStoppingPhaseFiber
          S B N d L m)) :
    unconditionalSourcePhysicalCleanedFullBilateralStateIsometry
        phaseSplit j
      (toLp 2
        (((unconditionalActualCleanedSelectedFullStageUnitary
              phaseSplit Q width schedule ξ spectralA A j :
              Matrix (UnconditionalSourcePhysicalStoppingPhaseFiber
                S B N d L m)
                (UnconditionalSourcePhysicalStoppingPhaseFiber
                  S B N d L m) ℂ) ⊗ₖ
            (unconditionalActualCleanedSelectedFullStageUnitary
              phaseSplit Q width schedule ζ spectralB C j :
              Matrix (UnconditionalSourcePhysicalStoppingPhaseFiber
                S B N d L m)
                (UnconditionalSourcePhysicalStoppingPhaseFiber
                  S B N d L m) ℂ)).mulVec
          (ofLp z))) =
      unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalActualCleanedSelectedStageBucketUnitary
            Q (width (schedule j)) ξ A *
          unconditionalActualCleanedSelectedStageSpectralUnitary
            (B := B) (m := m) spectralA)
        (unconditionalActualCleanedSelectedStageBucketUnitary
            Q (width (schedule j)) ζ C *
          unconditionalActualCleanedSelectedStageSpectralUnitary
            (B := B) (m := m) spectralB)
        (unconditionalSourcePhysicalCleanedFullBilateralStateIsometry
          phaseSplit j z) := by
  classical
  let e :
      UnconditionalSourcePhysicalStoppingPhaseFiber
          S B N d L m ≃
        UnconditionalSelectedCopyLocalIndex B d N m ×
          UnconditionalActualCleanedSelectedRetainedIndex
            (N := N) (d := d) j R :=
    unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
      (N := N) (d := d) (m := m) phaseSplit j
  let work :=
    unconditionalActualFixedSourceRetainedHistoryPairEquiv
      (N := N) (d := d) (R := R) j
  let UA :=
    unconditionalActualCleanedSelectedStageBucketUnitary
      Q (width (schedule j)) ξ A *
      unconditionalActualCleanedSelectedStageSpectralUnitary
        (B := B) (m := m) spectralA
  let UB :=
    unconditionalActualCleanedSelectedStageBucketUnitary
      Q (width (schedule j)) ζ C *
      unconditionalActualCleanedSelectedStageSpectralUnitary
        (B := B) (m := m) spectralB
  have transport :=
    unconditionalRegroupedSelectedRetainedReindexAction
      e work UA UB z
  simpa only [unconditionalActualCleanedSelectedFullStageUnitary,
    unconditionalSourcePhysicalCleanedFullBilateralStateIsometry,
    unconditionalActualFixedSourceFullBilateralRegroup_eq,
    e, work, UA, UB] using transport
end QuantumParallelRepetition
