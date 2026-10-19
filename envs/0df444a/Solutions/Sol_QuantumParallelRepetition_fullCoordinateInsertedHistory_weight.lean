-- Prove2me | solution 1 for QuantumParallelRepetition.fullCoordinateInsertedHistory_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/71c6da43-919c-4f73-9da4-d2ae2d14cf50

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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n) (hiD : i ∉ D)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y) :
    fullHistoryWeight G (fullCoordinateInsertedHistory D L i r x y) =
      fullCoordinateBaseWeight G D L i r * G.questionWeight x y := by
  classical
  have hremaining :
      (∏ j : {j : Fin n //
        j ∈ fullHistoryRemaining n (insert i D) L},
        G.marginalY
          ((fullCoordinateInsertedHistory D L i r x y).bobRemaining j)) =
      ∏ j : {j : Fin n //
        j ∈ fullHistoryRemaining n D (insert i L)},
        G.marginalY (r.bobRemaining j) := by
    let e := fullHistoryRemainingInsertedEquiv D L i
    calc
      (∏ j : {j : Fin n //
        j ∈ fullHistoryRemaining n (insert i D) L},
        G.marginalY
          ((fullCoordinateInsertedHistory D L i r x y).bobRemaining j)) =
        ∏ j : {j : Fin n //
          j ∈ fullHistoryRemaining n (insert i D) L},
          G.marginalY (r.bobRemaining (e j)) := by
            apply Finset.prod_congr rfl
            intro j _
            rfl
      _ = _ := e.prod_comp (fun j => G.marginalY (r.bobRemaining j))
  have hpair (j : {j : Fin n // j ∈ D}) :
      G.questionWeight
        ((fullCoordinateInsertedHistory D L i r x y).aliceConditioned
          ⟨j, Finset.mem_insert_of_mem j.property⟩)
        ((fullCoordinateInsertedHistory D L i r x y).bobConditioned
          ⟨j, Finset.mem_insert_of_mem j.property⟩) =
      G.questionWeight (r.aliceConditioned j) (r.bobConditioned j) := by
    have hj : (j : Fin n) ≠ i := by
      intro he
      exact hiD (he ▸ j.property)
    simp [fullCoordinateInsertedHistory,
      fullCoordinateAnswerExtension, hj]
  unfold fullHistoryWeight fullCoordinateBaseWeight
  change
    (∏ j : {j : Fin n // j ∈ insert i D},
      G.questionWeight
        ((fullCoordinateInsertedHistory D L i r x y).aliceConditioned j)
        ((fullCoordinateInsertedHistory D L i r x y).bobConditioned j)) *
    (∏ j : {j : Fin n // j ∈ L},
      G.marginalX (r.aliceRevealed j)) *
    (∏ j : {j : Fin n //
      j ∈ fullHistoryRemaining n (insert i D) L},
      G.marginalY
        ((fullCoordinateInsertedHistory D L i r x y).bobRemaining j)) = _
  rw [finsetSubtype_prod_insert D i hiD]
  rw [hremaining]
  simp_rw [hpair]
  simp [fullCoordinateInsertedHistory,
    fullCoordinateAnswerExtension]
  ring
end QuantumParallelRepetition
