-- Prove2me | solution 1 for QuantumParallelRepetition.fullCoordinateWeightedInsertedSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/77ee3d97-2d10-4341-97c9-61cb253ae5a3

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_fullCoordinateInsertedHistory_weight
import Theorems.Thm_QuantumParallelRepetition_fullCoordinateInsertedHistory_winIndicator_eq
import Theorems.Thm_QuantumParallelRepetition_fullCoordinateInsertedHistory_sum
import Theorems.Thm_QuantumParallelRepetition_fullCoordinateAnswerExtension_sum

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
    (hiD : i ∉ D)
    (value : (h : FullSubsetHistory X Y n (insert i D) L) →
      ({j : Fin n // j ∈ insert i D} → A) →
      ({j : Fin n // j ∈ insert i D} → B) → ℝ) :
    (∑ h : FullSubsetHistory X Y n (insert i D) L,
      ∑ α : {j : Fin n // j ∈ insert i D} → A,
      ∑ β : {j : Fin n // j ∈ insert i D} → B,
        fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
          value h α β) =
      ∑ r : FullCoordinateRevealHistory X Y n D L i,
      ∑ α : {j : Fin n // j ∈ D} → A,
      ∑ β : {j : Fin n // j ∈ D} → B,
        fullCoordinateBaseWeight G D L i r *
          fullCoordinateBaseWinIndicator G D L i r α β *
          (∑ x : X, ∑ y : Y, G.questionWeight x y *
            (∑ a : A, ∑ b : B,
              (if G.predicate x y a b = true then 1 else 0) *
                value (fullCoordinateInsertedHistory D L i r x y)
                  (fullCoordinateAnswerExtension D i α a)
                  (fullCoordinateAnswerExtension D i β b))) := by
  classical
  calc
    (∑ h : FullSubsetHistory X Y n (insert i D) L,
      ∑ α : {j : Fin n // j ∈ insert i D} → A,
      ∑ β : {j : Fin n // j ∈ insert i D} → B,
        fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
          value h α β) =
      ∑ r : FullCoordinateRevealHistory X Y n D L i,
      ∑ x : X, ∑ y : Y,
      ∑ α : {j : Fin n // j ∈ insert i D} → A,
      ∑ β : {j : Fin n // j ∈ insert i D} → B,
        fullHistoryWeight G
            (fullCoordinateInsertedHistory D L i r x y) *
          fullHistoryWinIndicator G
            (fullCoordinateInsertedHistory D L i r x y) α β *
          value (fullCoordinateInsertedHistory D L i r x y) α β :=
      fullCoordinateInsertedHistory_sum D L i hiD
        (fun h =>
          ∑ α : {j : Fin n // j ∈ insert i D} → A,
          ∑ β : {j : Fin n // j ∈ insert i D} → B,
            fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
              value h α β)
    _ =
      ∑ r : FullCoordinateRevealHistory X Y n D L i,
      ∑ x : X, ∑ y : Y,
      ∑ α : {j : Fin n // j ∈ D} → A, ∑ a : A,
      ∑ β : {j : Fin n // j ∈ D} → B, ∑ b : B,
        fullHistoryWeight G
            (fullCoordinateInsertedHistory D L i r x y) *
          fullHistoryWinIndicator G
            (fullCoordinateInsertedHistory D L i r x y)
            (fullCoordinateAnswerExtension D i α a)
            (fullCoordinateAnswerExtension D i β b) *
          value (fullCoordinateInsertedHistory D L i r x y)
            (fullCoordinateAnswerExtension D i α a)
            (fullCoordinateAnswerExtension D i β b) := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [fullCoordinateAnswerExtension_sum (T := A) D i hiD]
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro a _
      rw [fullCoordinateAnswerExtension_sum (T := B) D i hiD]
    _ =
      ∑ r : FullCoordinateRevealHistory X Y n D L i,
      ∑ α : {j : Fin n // j ∈ D} → A,
      ∑ β : {j : Fin n // j ∈ D} → B,
      ∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B,
        fullHistoryWeight G
            (fullCoordinateInsertedHistory D L i r x y) *
          fullHistoryWinIndicator G
            (fullCoordinateInsertedHistory D L i r x y)
            (fullCoordinateAnswerExtension D i α a)
            (fullCoordinateAnswerExtension D i β b) *
          value (fullCoordinateInsertedHistory D L i r x y)
            (fullCoordinateAnswerExtension D i α a)
            (fullCoordinateAnswerExtension D i β b) := by
      apply Finset.sum_congr rfl
      intro r _
      calc
        (∑ x : X, ∑ y : Y,
          ∑ α : {j : Fin n // j ∈ D} → A, ∑ a : A,
          ∑ β : {j : Fin n // j ∈ D} → B, ∑ b : B,
            fullHistoryWeight G
                (fullCoordinateInsertedHistory D L i r x y) *
              fullHistoryWinIndicator G
                (fullCoordinateInsertedHistory D L i r x y)
                (fullCoordinateAnswerExtension D i α a)
                (fullCoordinateAnswerExtension D i β b) *
              value (fullCoordinateInsertedHistory D L i r x y)
                (fullCoordinateAnswerExtension D i α a)
                (fullCoordinateAnswerExtension D i β b)) =
          ∑ x : X, ∑ y : Y,
          ∑ α : {j : Fin n // j ∈ D} → A,
          ∑ β : {j : Fin n // j ∈ D} → B,
          ∑ a : A, ∑ b : B,
            fullHistoryWeight G
                (fullCoordinateInsertedHistory D L i r x y) *
              fullHistoryWinIndicator G
                (fullCoordinateInsertedHistory D L i r x y)
                (fullCoordinateAnswerExtension D i α a)
                (fullCoordinateAnswerExtension D i β b) *
              value (fullCoordinateInsertedHistory D L i r x y)
                (fullCoordinateAnswerExtension D i α a)
                (fullCoordinateAnswerExtension D i β b) := by
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro y _
            apply Finset.sum_congr rfl
            intro α _
            rw [Finset.sum_comm]
        _ = _ := finite_sum_four_swap (fun x y α β =>
          ∑ a : A, ∑ b : B,
            fullHistoryWeight G
                (fullCoordinateInsertedHistory D L i r x y) *
              fullHistoryWinIndicator G
                (fullCoordinateInsertedHistory D L i r x y)
                (fullCoordinateAnswerExtension D i α a)
                (fullCoordinateAnswerExtension D i β b) *
              value (fullCoordinateInsertedHistory D L i r x y)
                (fullCoordinateAnswerExtension D i α a)
                (fullCoordinateAnswerExtension D i β b))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro β _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [fullCoordinateInsertedHistory_weight G D L i hiD r x y]
      rw [fullCoordinateInsertedHistory_winIndicator_eq
        G D L i hiD r x y α a β b]
      ring
end QuantumParallelRepetition
