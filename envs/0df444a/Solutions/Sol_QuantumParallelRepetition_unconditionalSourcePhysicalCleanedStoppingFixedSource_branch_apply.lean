-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalSourcePhysicalCleanedStoppingFixedSource_branch_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/d916808b-8962-4de9-b980-3de8164cbc9f

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalSourcePhysicalStoppingTargetFirst_branch_apply
import Theorems.Thm_QuantumParallelRepetition_unconditionalSourcePhysicalCleanedStoppingFixedSource_physicalAction

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
    {S B N d L m : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (r s : Fin (L + 1))
    (φ ψ : DSVDensityRationalPublicMultiscalePhaseIndex S B)
    (a b : DSVUniformDensityIndependentHistoryLocalIndex
      (L + 1) N d)
    (i k : Fin m) :
    actualStoppingBranchVector
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
          S B N d L m)) r s
      (⟨(φ, a), i⟩, ⟨(ψ, b), k⟩) =
        ePRState
          (Fintype.card
            (DSVDensityRationalPublicMultiscalePhase S B))
          (φ, ψ) *
        dSVDensityRationalHeterogeneousActualPhysicalState
          N width schedule ξ ζ (⟨r, a⟩, ⟨s, b⟩) *
        embezzlementState m (i, k) := by
  rw [unconditionalSourcePhysicalCleanedStoppingFixedSource_physicalAction]
  exact
    unconditionalSourcePhysicalStoppingTargetFirst_branch_apply
      width schedule ξ ζ r s φ ψ a b i k
end QuantumParallelRepetition
