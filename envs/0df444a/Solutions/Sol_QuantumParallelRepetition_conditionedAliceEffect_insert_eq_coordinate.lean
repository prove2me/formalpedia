-- Prove2me | solution 1 for QuantumParallelRepetition.conditionedAliceEffect_insert_eq_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/8d714741-bc3f-4763-9857-9c55e099ac13

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
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (i : Fin n) (hiD : i ∉ D)
    (α : {j : Fin n // j ∈ D} → A)
    (a : A) (xs : Fin n → X) :
    conditionedAliceEffect G n S (insert i D)
      (fullCoordinateAnswerExtension D i α a) xs =
      conditionedAliceCoordinateEffect G n S D α xs i a := by
  classical
  unfold conditionedAliceEffect conditionedAliceCoordinateEffect
  apply Finset.sum_congr rfl
  intro answers _
  have hiff :
      (∀ (j : Fin n) (hj : j ∈ insert i D),
        answers j = fullCoordinateAnswerExtension D i α a ⟨j, hj⟩) ↔
      ((∀ (j : Fin n) (hj : j ∈ D), answers j = α ⟨j, hj⟩) ∧
        answers i = a) := by
    constructor
    · intro h
      constructor
      · intro j hj
        have hji : j ≠ i := by
          intro he
          exact hiD (he ▸ hj)
        simpa [fullCoordinateAnswerExtension, hji]
          using h j (Finset.mem_insert_of_mem hj)
      · simpa [fullCoordinateAnswerExtension]
          using h i (Finset.mem_insert_self i D)
    · rintro ⟨hD, ha⟩ j hj
      by_cases hji : j = i
      · subst j
        simpa [fullCoordinateAnswerExtension] using ha
      · have hjD := (Finset.mem_insert.mp hj).resolve_left hji
        simpa [fullCoordinateAnswerExtension, hji] using hD j hjD
  by_cases h :
      ∀ (j : Fin n) (hj : j ∈ insert i D),
        answers j = fullCoordinateAnswerExtension D i α a ⟨j, hj⟩
  · simp only [if_pos h, if_pos (hiff.mp h)]
  · have hnot := mt hiff.mpr h
    simp only [if_neg h, if_neg hnot]
end QuantumParallelRepetition
