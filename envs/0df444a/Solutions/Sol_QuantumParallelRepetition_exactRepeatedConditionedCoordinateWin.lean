-- Prove2me | solution 1 for QuantumParallelRepetition.exactRepeatedConditionedCoordinateWin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/985332a2-42c6-4ac3-b83f-71ce5ec0731e

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (i : Fin n) :
    (∑ outcome : ExactOutcome X Y A B n,
      if repeatedCoordinateWin G n i outcome = true then
        repeatedConditionedOutcomeLaw G n S D outcome
      else 0) =
    (strategyEventLaw (G.repeat n) S).eventMass
        (FiniteEventLaw.winEvent
          (repeatedCoordinateWin G n) (insert i D)) /
        repeatedPostselectionMass G n S D := by
  classical
  have accepted_as_indicator :
      (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent
            (repeatedCoordinateWin G n) (insert i D)) =
        ∑ outcome : ExactOutcome X Y A B n,
          if outcome ∈ FiniteEventLaw.winEvent
              (repeatedCoordinateWin G n) (insert i D) then
            (strategyEventLaw (G.repeat n) S).weight outcome
          else 0 := by
    simp [FiniteEventLaw.eventMass]
  rw [accepted_as_indicator]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases winning : repeatedCoordinateWin G n i outcome = true
  · simp [repeatedConditionedOutcomeLaw,
      conditionedEventDistribution,
      repeatedPostselectionMass, postselectionMass,
      FiniteEventLaw.winEvent, winning, ite_div]
  · simp [FiniteEventLaw.winEvent, winning]
end QuantumParallelRepetition
