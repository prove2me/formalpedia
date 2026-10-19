-- Prove2me | solution 1 for QuantumParallelRepetition.fullCoordinateInsertedHistory_winIndicator_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/64a94539-0ea5-4332-9064-b828a317982f

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
    (D L : Finset (Fin n)) (i : Fin n) (hiD : i ∉ D)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y)
    (α : {j : Fin n // j ∈ D} → A) (a : A)
    (β : {j : Fin n // j ∈ D} → B) (b : B) :
    fullHistoryWinIndicator G
      (fullCoordinateInsertedHistory D L i r x y)
      (fullCoordinateAnswerExtension D i α a)
      (fullCoordinateAnswerExtension D i β b) =
      fullCoordinateBaseWinIndicator G D L i r α β *
        (if G.predicate x y a b = true then 1 else 0) := by
  classical
  have hiff :
      (∀ j : {j : Fin n // j ∈ insert i D},
        G.predicate
          ((fullCoordinateInsertedHistory D L i r x y).aliceConditioned j)
          ((fullCoordinateInsertedHistory D L i r x y).bobConditioned j)
          (fullCoordinateAnswerExtension D i α a j)
          (fullCoordinateAnswerExtension D i β b j) = true) ↔
      ((∀ j : {j : Fin n // j ∈ D},
        G.predicate (r.aliceConditioned j) (r.bobConditioned j)
          (α j) (β j) = true) ∧ G.predicate x y a b = true) := by
    constructor
    · intro h
      constructor
      · intro j
        have hji : (j : Fin n) ≠ i := by
          intro he
          exact hiD (he ▸ j.property)
        simpa [fullCoordinateInsertedHistory,
          fullCoordinateAnswerExtension, hji] using
          h ⟨j, Finset.mem_insert_of_mem j.property⟩
      · simpa [fullCoordinateInsertedHistory,
          fullCoordinateAnswerExtension] using
          h ⟨i, Finset.mem_insert_self i D⟩
    · rintro ⟨hD, hi⟩ j
      by_cases hji : (j : Fin n) = i
      · have hjsub :
            j = (⟨i, Finset.mem_insert_self i D⟩ :
              {j : Fin n // j ∈ insert i D}) := Subtype.ext hji
        subst j
        simpa [fullCoordinateInsertedHistory,
          fullCoordinateAnswerExtension] using hi
      · have hjD : (j : Fin n) ∈ D :=
          (Finset.mem_insert.mp j.property).resolve_left hji
        simpa [fullCoordinateInsertedHistory,
          fullCoordinateAnswerExtension, hji] using hD ⟨j, hjD⟩
  change
    (if ∀ j : {j : Fin n // j ∈ insert i D},
      G.predicate
        ((fullCoordinateInsertedHistory D L i r x y).aliceConditioned j)
        ((fullCoordinateInsertedHistory D L i r x y).bobConditioned j)
        (fullCoordinateAnswerExtension D i α a j)
        (fullCoordinateAnswerExtension D i β b j) = true
      then (1 : ℝ) else 0) =
      (if ∀ j : {j : Fin n // j ∈ D},
        G.predicate (r.aliceConditioned j) (r.bobConditioned j)
          (α j) (β j) = true then (1 : ℝ) else 0) *
      (if G.predicate x y a b = true then (1 : ℝ) else 0)
  split_ifs with hall hD hi <;> aesop
end QuantumParallelRepetition
