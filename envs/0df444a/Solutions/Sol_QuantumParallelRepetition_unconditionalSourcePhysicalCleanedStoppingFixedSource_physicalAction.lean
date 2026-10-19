-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalSourcePhysicalCleanedStoppingFixedSource_physicalAction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/08d841e9-6ba8-465a-8018-f92b81232315

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalSourcePhysicalCleanedStoppingLocalAction_reindex

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
    (ξ ζ : BipartiteUnitVector d) :
    actualStoppingQuestionLocalAction
      (unconditionalSourcePhysicalCleanedTargetFirstUnitary
        S B N d L m
        (dSVDensityRationalHeterogeneousTargetFirstSpectralAlice
          S B N d L m width schedule ξ))
      (unconditionalSourcePhysicalCleanedTargetFirstUnitary
        S B N d L m
        (dSVDensityRationalHeterogeneousTargetFirstSpectralBob
          S B N d L m width schedule ζ))
      (unconditionalSourcePhysicalCleanedStoppingFixedSource
        S B N d L m) =
      unconditionalSourcePhysicalStoppingTargetFirstStateEquiv
        S B N d L m
        (dSVDensityRationalHeterogeneousOriginalStoppedState
          S B N d L m width schedule ξ ζ) := by
  unfold unconditionalSourcePhysicalCleanedStoppingFixedSource
  rw [unconditionalSourcePhysicalCleanedStoppingLocalAction_reindex]
  rfl
end QuantumParallelRepetition
