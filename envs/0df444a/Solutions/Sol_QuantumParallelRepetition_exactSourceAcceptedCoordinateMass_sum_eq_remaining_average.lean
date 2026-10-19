-- Prove2me | solution 1 for QuantumParallelRepetition.exactSourceAcceptedCoordinateMass_sum_eq_remaining_average
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/eb2c00d3-b644-4bf8-ae4f-77fb2612af0b

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_exactSourceAcceptedCoordinateMass_sum
import Theorems.Thm_QuantumParallelRepetition_exactRepeatedConditionedCoordinateWin

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
    (D : Finset (Fin n)) :
    (∑ t : ExactLocallySampleableTuple X Y A B D,
      exactSourceAcceptedCoordinateMass G n S D t) =
      (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        (∑ i : SourceRemainingCoordinate D,
          (strategyEventLaw (G.repeat n) S).eventMass
            (FiniteEventLaw.winEvent
              (repeatedCoordinateWin G n) (insert i.val D)) /
            repeatedPostselectionMass G n S D) := by
  classical
  rw [exactSourceAcceptedCoordinateMass_sum]
  unfold exactPostselectedJointLaw
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc
    (∑ outcome : ExactOutcome X Y A B n,
      ∑ seed : ExactRemainingSeed D,
        if repeatedCoordinateWin G n seed.coordinate.val outcome = true
        then exactSeedWeight seed *
          repeatedConditionedOutcomeLaw G n S D outcome
        else 0) =
      ∑ outcome : ExactOutcome X Y A B n,
        ∑ seed : ExactRemainingSeed D,
          exactSeedWeight seed *
            (if repeatedCoordinateWin G n seed.coordinate.val outcome = true
             then repeatedConditionedOutcomeLaw G n S D outcome
             else 0) := by
          apply Finset.sum_congr rfl
          intro outcome _
          apply Finset.sum_congr rfl
          intro seed _
          split <;> simp
    _ = ∑ outcome : ExactOutcome X Y A B n,
        ∑ i : SourceRemainingCoordinate D,
          (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
            (if repeatedCoordinateWin G n i.val outcome = true
             then repeatedConditionedOutcomeLaw G n S D outcome
             else 0) := by
          apply Finset.sum_congr rfl
          intro outcome _
          exact exactSeedWeight_coordinate_sum
            (M := SourceRemainingCoordinate D)
            (fun i =>
              if repeatedCoordinateWin G n i.val outcome = true
              then repeatedConditionedOutcomeLaw G n S D outcome
              else 0)
    _ = (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        (∑ i : SourceRemainingCoordinate D,
          ∑ outcome : ExactOutcome X Y A B n,
            if repeatedCoordinateWin G n i.val outcome = true
            then repeatedConditionedOutcomeLaw G n S D outcome
            else 0) := by
          rw [Finset.sum_comm, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact exactRepeatedConditionedCoordinateWin
        G n S D i.val
end QuantumParallelRepetition
