-- Prove2me | solution 1 for QuantumParallelRepetition.fullCoordinateInsertedBobQuestion_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/0bdc0775-9574-4d9d-a63e-88e554ef4f08

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
    (hidden : {j : Fin n // j ∈ L} → Y) :
    fullHistoryBobQuestion
      (fullCoordinateInsertedHistory D L i r x y) hidden =
      fullHistoryBobQuestion
        (fullCoordinateOldHistory D L i r y) hidden := by
  classical
  funext j
  by_cases hjD : j ∈ D
  · have hji : j ≠ i := by
      intro he
      exact hiD (he ▸ hjD)
    simp [fullHistoryBobQuestion, fullCoordinateInsertedHistory,
      fullCoordinateAnswerExtension, fullCoordinateOldHistory,
      hjD, hji]
  · by_cases hji : j = i
    · subst j
      simp [fullHistoryBobQuestion, fullCoordinateInsertedHistory,
        fullCoordinateAnswerExtension, fullCoordinateOldHistory,
        hiD, hiL]
    · by_cases hjL : j ∈ L
      · simp [fullHistoryBobQuestion,                     hjD, hji, hjL]
      · simp [fullHistoryBobQuestion, fullCoordinateInsertedHistory,
          fullCoordinateOldHistory,
          hjD, hji, hjL]
end QuantumParallelRepetition
