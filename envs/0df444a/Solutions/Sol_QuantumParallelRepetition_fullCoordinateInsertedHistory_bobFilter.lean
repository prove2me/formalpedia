-- Prove2me | solution 1 for QuantumParallelRepetition.fullCoordinateInsertedHistory_bobFilter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/889b48e5-fa0b-4e3a-9496-7c0bbe3a6444

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_conditionedBobEffect_insert_eq_coordinate
import Theorems.Thm_QuantumParallelRepetition_fullCoordinateInsertedBobQuestion_eq
import Theorems.Thm_QuantumParallelRepetition_fullCoordinateInsertedHiddenBobWeight_eq

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
    (β : {j : Fin n // j ∈ D} → B) (b : B) :
    fullHistoryBobFilter G n S (insert i D) L
      (fullCoordinateInsertedHistory D L i r x y)
      (fullCoordinateAnswerExtension D i β b) =
      fullCoordinateBobRefinementEffect G n S D L i r β y b := by
  classical
  change
    (∑ hidden : {j : Fin n // j ∈ L} → Y,
      fullHistoryHiddenBobWeight G
        (fullCoordinateInsertedHistory D L i r x y) hidden •
      conditionedBobEffect G n S (insert i D)
        (fullCoordinateAnswerExtension D i β b)
        (fullHistoryBobQuestion
          (fullCoordinateInsertedHistory D L i r x y) hidden)) =
      ∑ hidden : {j : Fin n // j ∈ L} → Y,
        fullHistoryHiddenBobWeight G
          (fullCoordinateOldHistory D L i r y) hidden •
        conditionedBobCoordinateEffect G n S D β
          (fullHistoryBobQuestion
            (fullCoordinateOldHistory D L i r y) hidden) i b
  apply Finset.sum_congr rfl
  intro hidden _
  rw [fullCoordinateInsertedHiddenBobWeight_eq G D L i r x y hidden]
  rw [fullCoordinateInsertedBobQuestion_eq D L i hiD hiL r x y hidden]
  rw [conditionedBobEffect_insert_eq_coordinate G n S D i hiD β b]
end QuantumParallelRepetition
