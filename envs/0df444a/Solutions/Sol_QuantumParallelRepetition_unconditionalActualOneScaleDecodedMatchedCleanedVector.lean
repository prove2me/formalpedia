-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualOneScaleDecodedMatchedCleanedVector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/b1af20d3-8689-43f5-894f-949fc0ee8ad1

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualOneScalePhysicalQuestionDecodedMatchedBranch

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
    {F X Y : Type} {P N d L m : ℕ}
    (Q : ℕ) (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (ξ : F → X → BipartiteUnitVector d)
    (ζ : F → Y → BipartiteUnitVector d)
    (A C : Fin P → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (grid : 0 < N)
    (flag : F) (x : X) (y : Y) (j : Fin L)
    (positive : 0 < width (schedule j)) :
    unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P
          (conjugateUnitary
            (dSVDensityRationalCanonicalAliceBasis (ξ flag x))))
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P
          (conjugateUnitary
            (dSVUniformDensityThresholdLeftBobBasis (ζ flag y))))
        (unconditionalSourcePhysicalCleanedFullBilateralStateIsometry
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
                1 P N d L m)) j.succ j.succ)) =
      integratorActualC485CleanedVector
        (S := 1) (B := P) (N := N) (d := d) (L := L) (m := m)
        Q width schedule (ξ flag x) (ζ flag y) A C j := by
  classical
  have decoded :=
    unconditionalActualOneScalePhysicalQuestionDecodedMatchedBranch
      Q width schedule ξ ζ A C grid flag x y j positive
  change
    unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P
          (conjugateUnitary
            (dSVDensityRationalCanonicalAliceBasis (ξ flag x))))
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P
          (conjugateUnitary
            (dSVUniformDensityThresholdLeftBobBasis (ζ flag y))))
        _ =
      unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P
          (conjugateUnitary
            (dSVDensityRationalCanonicalAliceBasis (ξ flag x))))
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P
          (conjugateUnitary
            (dSVUniformDensityThresholdLeftBobBasis (ζ flag y))))
        _
  rw [decoded]
end QuantumParallelRepetition
