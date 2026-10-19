-- Prove2me | solution 1 for QuantumParallelRepetition.fullCoordinateInsertedHistory_aliceFilter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/a413b285-ac52-4576-9ae1-8f410bf49178

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_conditionedAliceEffect_insert_eq_coordinate
import Theorems.Thm_QuantumParallelRepetition_fullCoordinateInsertedAliceQuestion_eq
import Theorems.Thm_QuantumParallelRepetition_fullCoordinateInsertedHiddenAliceWeight_eq

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
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y)
    (α : {j : Fin n // j ∈ D} → A) (a : A) :
    fullHistoryAliceFilter G n S (insert i D) L
      (fullCoordinateInsertedHistory D L i r x y)
      (fullCoordinateAnswerExtension D i α a) =
      fullCoordinateAliceRefinementEffect G n S D L i r α x a := by
  classical
  change
    (∑ hidden : {j : Fin n //
      j ∈ fullHistoryRemaining n (insert i D) L} → X,
      fullHistoryHiddenAliceWeight G
        (fullCoordinateInsertedHistory D L i r x y) hidden •
      conditionedAliceEffect G n S (insert i D)
        (fullCoordinateAnswerExtension D i α a)
        (fullHistoryAliceQuestion
          (fullCoordinateInsertedHistory D L i r x y) hidden)) =
      ∑ hidden : {j : Fin n //
        j ∈ fullHistoryRemaining n D (insert i L)} → X,
        fullHistoryHiddenAliceWeight G
          (fullCoordinateNewHistory D L i r x) hidden •
        conditionedAliceCoordinateEffect G n S D α
          (fullHistoryAliceQuestion
            (fullCoordinateNewHistory D L i r x) hidden) i a
  calc
    (∑ hidden : {j : Fin n //
      j ∈ fullHistoryRemaining n (insert i D) L} → X,
      fullHistoryHiddenAliceWeight G
        (fullCoordinateInsertedHistory D L i r x y) hidden •
      conditionedAliceEffect G n S (insert i D)
        (fullCoordinateAnswerExtension D i α a)
        (fullHistoryAliceQuestion
          (fullCoordinateInsertedHistory D L i r x y) hidden)) =
      ∑ hidden : {j : Fin n //
        j ∈ fullHistoryRemaining n D (insert i L)} → X,
        fullHistoryHiddenAliceWeight G
          (fullCoordinateInsertedHistory D L i r x y)
          ((fullCoordinateInsertedHiddenAliceEquiv
            (X := X) D L i).symm hidden) •
        conditionedAliceEffect G n S (insert i D)
          (fullCoordinateAnswerExtension D i α a)
          (fullHistoryAliceQuestion
            (fullCoordinateInsertedHistory D L i r x y)
            ((fullCoordinateInsertedHiddenAliceEquiv
              (X := X) D L i).symm hidden)) := by
        exact ((fullCoordinateInsertedHiddenAliceEquiv
          (X := X) D L i).symm.sum_comp
          (fun hidden =>
            fullHistoryHiddenAliceWeight G
              (fullCoordinateInsertedHistory D L i r x y) hidden •
            conditionedAliceEffect G n S (insert i D)
              (fullCoordinateAnswerExtension D i α a)
              (fullHistoryAliceQuestion
                (fullCoordinateInsertedHistory D L i r x y)
                hidden))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro hidden _
      rw [fullCoordinateInsertedHiddenAliceWeight_eq
        G D L i r x y hidden]
      rw [fullCoordinateInsertedAliceQuestion_eq
        D L i hiD hiL r x y hidden]
      rw [conditionedAliceEffect_insert_eq_coordinate
        G n S D i hiD α a]
end QuantumParallelRepetition
