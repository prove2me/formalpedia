-- Prove2me | solution 1 for QuantumParallelRepetition.exactSourceConditionalWinningProbability_eq_accepted_average
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/caddafa9-4fbc-477a-84aa-e7e2eca5714b

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_sourceHistoryAcceptedMass_eq_remaining_average
import Theorems.Thm_QuantumParallelRepetition_exactSourceAcceptedCoordinateMass_sum
import Theorems.Thm_QuantumParallelRepetition_exactSourceConditionalWinningProbability_expectation
import Theorems.Thm_QuantumParallelRepetition_exactSourceAcceptedCoordinateMass_sum_eq_remaining_average

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
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D) :
    (∑ t : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D t *
        exactSourceConditionalWinningProbability G n S D t) =
      sourceHistoryAcceptedMass G n S D /
        repeatedPostselectionMass G n S D := by
  rw [exactSourceConditionalWinningProbability_expectation
    G n S D positive,
    ← exactSourceAcceptedCoordinateMass_sum,
    exactSourceAcceptedCoordinateMass_sum_eq_remaining_average,
    sourceHistoryAcceptedMass_eq_remaining_average]
  have cardinality :
      Fintype.card (SourceRemainingCoordinate D) =
        (Finset.univ \ D).card := by
    simpa only [Fintype.card_fin] using Fintype.card_congr
      (Finset.equivFin (Finset.univ \ D))
  push_cast [cardinality]
  rw [← Finset.sum_div]
  ring
end QuantumParallelRepetition
