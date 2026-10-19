-- Prove2me | solution 1 for QuantumParallelRepetition.exactSourceConditionalWinningProbability_gt_of_uniform_failure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/cd93fdc2-2c8d-4326-ac5d-3089aab5d7b5

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_sourceHistoryAcceptedMass_gt_of_greedy
import Theorems.Thm_QuantumParallelRepetition_exactSourceConditionalWinningProbability_eq_accepted_average
import Theorems.Thm_QuantumParallelRepetition_exactSource_failure_sum_lt_of_uniform

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
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    {δ : ℝ}
    (failure : uniformRemainingFailure
      (strategyEventLaw (G.repeat n) S)
      (repeatedCoordinateWin G n) D < δ) :
    1 - δ <
      ∑ t : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableLaw G n S D t *
          exactSourceConditionalWinningProbability G n S D t := by
  rw [exactSourceConditionalWinningProbability_eq_accepted_average
    G n S D positive]
  have numerator := exactSource_failure_sum_lt_of_uniform
    G n S D remaining positive failure
  have accepted := sourceHistoryAcceptedMass_gt_of_greedy
    G n S D remaining numerator
  apply (lt_div_iff₀ positive).mpr
  exact accepted
end QuantumParallelRepetition
