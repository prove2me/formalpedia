-- Prove2me | solution 1 for QuantumParallelRepetition.sourceHistoryAcceptedMass_eq_remaining_average
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/b038f657-28d4-490d-b918-ad19786c0257

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_sourceRemainingPermutationCoordinate_sum
import Theorems.Thm_QuantumParallelRepetition_sourceHistoryAcceptedMass_eq_uniform

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (D : Finset (Fin n)) :
    sourceHistoryAcceptedMass G n S D =
      (∑ i : SourceRemainingCoordinate D,
        (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
            (insert i.val D))) /
        ((Finset.univ \ D).card : ℝ) := by
  classical
  rw [sourceHistoryAcceptedMass_eq_uniform]
  have hperm := sourceRemainingPermutation_card_pos D
  unfold sourceUniformPermutationAverage
  simp_rw [sourceRemainingPermutationCoordinate_sum D _
    (fun i : Fin n =>
      (strategyEventLaw (G.repeat n) S).eventMass
        (FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
          (insert i D)))]
  have hsum :
      (∑ _π : SourceRemainingPermutation D,
        ∑ i : SourceRemainingCoordinate D,
          (strategyEventLaw (G.repeat n) S).eventMass
            (FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
              (insert i.val D))) =
      (Fintype.card (SourceRemainingPermutation D) : ℝ) *
        (∑ i : SourceRemainingCoordinate D,
          (strategyEventLaw (G.repeat n) S).eventMass
            (FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
              (insert i.val D))) := by simp
  rw [hsum]
  exact mul_div_mul_left _ _ hperm.ne'
end QuantumParallelRepetition
