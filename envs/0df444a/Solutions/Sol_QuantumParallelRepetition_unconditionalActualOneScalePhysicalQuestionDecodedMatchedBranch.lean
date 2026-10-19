-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualOneScalePhysicalQuestionDecodedMatchedBranch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/d825a931-d475-4cfa-bdf0-e6a5f16165d5

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualOneScaleFixedSourcePhysicalQuestionAction
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualOneScaleFixedSourceDecodedMatchedBranch

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
    {F X Y : Type} {P N d L m : ℕ}
    (Q : ℕ) (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (ξ : F → X → BipartiteUnitVector d)
    (ζ : F → Y → BipartiteUnitVector d)
    (A C : Fin P → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (grid : 0 < N)
    (flag : F) (x : X) (y : Y) (j : Fin L)
    (positive : 0 < width (schedule j)) :
    unconditionalSourcePhysicalCleanedFullBilateralStateIsometry
        (unconditionalActualOneScaleFixedSourcePhaseSplit P) j
        (actualStoppingBranchVector
          (actualStoppingQuestionLocalAction
            (physical8OneScaleActualAliceStoppingUnitary
              (P := P) (N := N) (d := d) (L := L) (m := m)
              (unconditionalActualOneScaleFixedSourcePhaseSplit P)
              Q width schedule ξ A flag x)
            (physical8OneScaleActualBobStoppingUnitary
              (P := P) (N := N) (d := d) (L := L) (m := m)
              (unconditionalActualOneScaleFixedSourcePhaseSplit P)
              Q width schedule ζ C flag y)
            (unconditionalSourcePhysicalCleanedStoppingFixedSource
              1 P N d L m)) j.succ j.succ) =
      unconditionalSelectedCopyCleanedMatchedBranch
        (N := N) (B := P) (m := m)
        Q width schedule (ξ flag x) (ζ flag y) A C j
        (unconditionalActualCanonicalRetainedPhaseTail
          (S := 1) (B := P) (N := N) (d := d) (L := L) j) := by
  rw [unconditionalActualOneScaleFixedSourcePhysicalQuestionAction]
  exact unconditionalActualOneScaleFixedSourceDecodedMatchedBranch
    Q width schedule (ξ flag x) (ζ flag y) A C j positive grid
end QuantumParallelRepetition
