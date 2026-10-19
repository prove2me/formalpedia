-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairSourcePhysicalStopBorn_eq_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/54391f56-0f75-42a0-ab32-5d4d3cd9d698

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
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
namespace QuantumParallelRepetition
theorem _root_.solution
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (a₀ : A) (b₀ : B)
    {P N L m : ℕ} (Q : ℕ)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (UA UB : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) (y : Y) (j : Fin L) :
    let d := Fintype.card (ExactGlobalHistoryLocalIndex G n S D)
    let PA := unconditionalActualFairSourceAliceFlagPOVM
      G n S D denominator numerator nonempty a₀ P N L m flag
    let PB := unconditionalActualFairSourceBobFlagPOVM
      G n S D denominator numerator nonempty b₀ P N L m flag
    let stopped := actualStoppingBranchVector
      (actualStoppingQuestionLocalAction
        (unconditionalActualFairSourceAliceStoppingUnitary
          (P := P) (N := N) (L := L) (m := m)
          G n S D denominator numerator nonempty
          Q width schedule UA flag x)
        (unconditionalActualFairSourceBobStoppingUnitary
          (P := P) (N := N) (L := L) (m := m)
          G n S D denominator numerator nonempty
          Q width schedule UB flag y)
        (unconditionalSourcePhysicalCleanedStoppingFixedSource
          1 P N d L m)) j.succ j.succ
    unconditionalActualFairSourcePhysicalStopBorn
        G n S D denominator numerator nonempty a₀ b₀
        Q width schedule UA UB flag x y j =
      unconditionalActualC485RawPhysicalVerifierBorn
        G (PA j.succ x) (PB j.succ y) x y stopped := by
  classical
  dsimp only
  rfl
end QuantumParallelRepetition
