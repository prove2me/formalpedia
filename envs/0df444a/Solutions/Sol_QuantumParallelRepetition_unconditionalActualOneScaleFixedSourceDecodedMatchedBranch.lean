-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualOneScaleFixedSourceDecodedMatchedBranch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/33117859-e971-4ac4-90e9-a0eac3548f11

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualFixedSourceDecodedMatchedBranch
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualOneScaleFlagControlledFiniteStageDecoder_eq

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
    {P N d L m : ℕ}
    (Q : ℕ) (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin P → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L)
    (positive : 0 < width (schedule j)) (grid : 0 < N) :
    unconditionalSourcePhysicalCleanedFullBilateralStateIsometry
        (unconditionalActualOneScaleFixedSourcePhaseSplit P) j
        (actualStoppingBranchVector
          (unconditionalActualOneScaleFixedSourceDecodedState
            Q width schedule ξ ζ A C) j.succ j.succ) =
      unconditionalSelectedCopyCleanedMatchedBranch
        (N := N) (B := P) (m := m)
        Q width schedule ξ ζ A C j
        (unconditionalActualCanonicalRetainedPhaseTail
          (S := 1) (B := P) (N := N) (d := d) (L := L) j) := by
  have sameScale : schedule j = (0 : Fin 1) :=
    Subsingleton.elim _ _
  have samePhase :
      (unconditionalActualMultiscalePhaseIndexEquiv
        (B := P) (schedule j)).symm =
        unconditionalActualOneScaleFixedSourcePhaseSplit P := by
    simp only [unconditionalActualOneScaleFixedSourcePhaseSplit]
    rw [sameScale]
  have decoded :=
    unconditionalActualFixedSourceDecodedMatchedBranch
      (S := 1) (B := P) (N := N) (d := d) (L := L) (m := m)
      Q width schedule ξ ζ A C j positive grid
  rw [samePhase] at decoded
  simpa only [unconditionalActualOneScaleFixedSourceDecodedState,
    unconditionalActualOneScaleFlagControlledFiniteStageDecoder_eq]
    using decoded
end QuantumParallelRepetition
