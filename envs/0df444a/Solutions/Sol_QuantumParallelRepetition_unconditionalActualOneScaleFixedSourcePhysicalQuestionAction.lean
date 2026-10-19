-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualOneScaleFixedSourcePhysicalQuestionAction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/466d3322-cce2-4eb2-aef2-b954e24b6f9f

import Mathlib
import Definitions.Def_QuantumParallelRepetition

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
    (flag : F) (x : X) (y : Y) :
    actualStoppingQuestionLocalAction
        (physical8OneScaleActualAliceStoppingUnitary
          (P := P) (N := N) (d := d) (L := L) (m := m)
          (unconditionalActualOneScaleFixedSourcePhaseSplit P)
          Q width schedule ξ A flag x)
        (physical8OneScaleActualBobStoppingUnitary
          (P := P) (N := N) (d := d) (L := L) (m := m)
          (unconditionalActualOneScaleFixedSourcePhaseSplit P)
          Q width schedule ζ C flag y)
        (unconditionalSourcePhysicalCleanedStoppingFixedSource
          1 P N d L m) =
      unconditionalActualOneScaleFixedSourceDecodedState
        Q width schedule (ξ flag x) (ζ flag y) A C := by
  classical
  unfold physical8OneScaleActualAliceStoppingUnitary
    physical8OneScaleActualBobStoppingUnitary
    unconditionalActualOneScaleFixedSourceDecodedState
    actualStoppingQuestionLocalAction
    dSVUniformDensityPhysicalAsyncSigmaContinuation
  simp only []
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_kronecker_mul]
  rfl
end QuantumParallelRepetition
