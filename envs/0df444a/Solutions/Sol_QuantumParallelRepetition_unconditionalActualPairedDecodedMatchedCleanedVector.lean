-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualPairedDecodedMatchedCleanedVector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/4ed7ffd6-b54e-4ac6-b91b-f39f1780881d

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualOneScaleDecodedMatchedCleanedVector
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualC485FullBilateralWorkRegroup

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
    let phase := unconditionalActualOneScaleFixedSourcePhaseSplit P
    let outer := unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
      (N := N) (d := d) (m := m) phase j
    let pair := unconditionalActualC485RetainedHistoryPairEquiv
      (P := P) (N := N) (d := d) j
    let stopped := actualStoppingBranchVector
      (actualStoppingQuestionLocalAction
        (physical8OneScaleActualAliceStoppingUnitary
          (P := P) (N := N) (d := d) (L := L) (m := m)
          phase Q width schedule ξ A flag x)
        (physical8OneScaleActualBobStoppingUnitary
          (P := P) (N := N) (d := d) (L := L) (m := m)
          phase Q width schedule ζ C flag y)
        (unconditionalSourcePhysicalCleanedStoppingFixedSource
          1 P N d L m)) j.succ j.succ
    unconditionalMixedConjugateSelectedBranchLocalAction
      (unconditionalMixedConjugateSigmaAtomLift
        (m := N * m) P
        (conjugateUnitary
          (dSVDensityRationalCanonicalAliceBasis (ξ flag x))))
      (unconditionalMixedConjugateSigmaAtomLift
        (m := N * m) P
        (conjugateUnitary
          (dSVUniformDensityThresholdLeftBobBasis (ζ flag y))))
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.prodCongr
          (Equiv.refl
            (UnconditionalSelectedCopyLocalIndex P d N m ×
             UnconditionalSelectedCopyLocalIndex P d N m)) pair)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (directDSVActualBilateralRetainedIndexEquiv
            outer outer) stopped)) =
      integratorActualC485CleanedVector
        (S := 1) (B := P) (N := N) (d := d) (L := L) (m := m)
        Q width schedule (ξ flag x) (ζ flag y) A C j := by
  dsimp only
  rw [unconditionalActualC485FullBilateralWorkRegroup]
  exact unconditionalActualOneScaleDecodedMatchedCleanedVector
    Q width schedule ξ ζ A C grid flag x y j positive
end QuantumParallelRepetition
