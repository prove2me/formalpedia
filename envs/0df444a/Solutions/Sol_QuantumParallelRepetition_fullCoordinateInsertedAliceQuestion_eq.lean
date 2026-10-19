-- Prove2me | solution 1 for QuantumParallelRepetition.fullCoordinateInsertedAliceQuestion_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/eda8daac-c990-4915-bb57-31e762aa4059

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y)
    (hidden : {j : Fin n //
      j ∈ fullHistoryRemaining n D (insert i L)} → X) :
    fullHistoryAliceQuestion
      (fullCoordinateInsertedHistory D L i r x y)
      ((fullCoordinateInsertedHiddenAliceEquiv (X := X) D L i).symm hidden) =
      fullHistoryAliceQuestion
        (fullCoordinateNewHistory D L i r x) hidden := by
  classical
  funext j
  by_cases hjD : j ∈ D
  · have hji : j ≠ i := by
      intro he
      exact hiD (he ▸ hjD)
    simp [fullHistoryAliceQuestion, fullCoordinateInsertedHistory,
      fullCoordinateAnswerExtension, fullCoordinateNewHistory,
      hjD, hji]
  · by_cases hji : j = i
    · subst j
      simp [fullHistoryAliceQuestion, fullCoordinateInsertedHistory,
        fullCoordinateAnswerExtension, fullCoordinateNewHistory,
        hiD, hiL]
    · by_cases hjL : j ∈ L
      · simp [fullHistoryAliceQuestion, fullCoordinateInsertedHistory,
          fullCoordinateNewHistory,
          hjD, hji, hjL]
      · simp [fullHistoryAliceQuestion,                     fullCoordinateInsertedHiddenAliceEquiv,
          fullHistoryRemainingInsertedEquiv, hjD, hji, hjL]
        congr 1
end QuantumParallelRepetition
