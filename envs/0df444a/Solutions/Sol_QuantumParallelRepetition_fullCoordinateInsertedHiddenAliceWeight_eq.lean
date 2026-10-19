-- Prove2me | solution 1 for QuantumParallelRepetition.fullCoordinateInsertedHiddenAliceWeight_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/0cb67095-b257-43cd-b2b0-3436e6fca3cc

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
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y)
    (hidden : {j : Fin n //
      j ∈ fullHistoryRemaining n D (insert i L)} → X) :
    fullHistoryHiddenAliceWeight G
      (fullCoordinateInsertedHistory D L i r x y)
      ((fullCoordinateInsertedHiddenAliceEquiv (X := X) D L i).symm hidden) =
      fullHistoryHiddenAliceWeight G
        (fullCoordinateNewHistory D L i r x) hidden := by
  classical
  let e := fullHistoryRemainingInsertedEquiv D L i
  unfold fullHistoryHiddenAliceWeight
  calc
    (∏ j : {j : Fin n //
      j ∈ fullHistoryRemaining n (insert i D) L},
      G.conditionalXGivenY
        ((fullCoordinateInsertedHistory D L i r x y).bobRemaining j)
        (((fullCoordinateInsertedHiddenAliceEquiv
          (X := X) D L i).symm hidden) j)) =
      ∏ j : {j : Fin n //
        j ∈ fullHistoryRemaining n (insert i D) L},
        G.conditionalXGivenY (r.bobRemaining (e j)) (hidden (e j)) := by
          apply Finset.prod_congr rfl
          intro j _
          rfl
    _ = ∏ j : {j : Fin n //
        j ∈ fullHistoryRemaining n D (insert i L)},
        G.conditionalXGivenY (r.bobRemaining j) (hidden j) :=
      e.prod_comp (fun j =>
        G.conditionalXGivenY (r.bobRemaining j) (hidden j))
    _ = _ := rfl
end QuantumParallelRepetition
