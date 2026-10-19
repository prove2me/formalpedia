-- Prove2me | solution 1 for QuantumParallelRepetition.exactSourceAcceptedCoordinateMass_eq_seeded_fair_born
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/5306eb91-efcd-409c-b56a-b4295def7e8e

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_exactSourceAcceptedCoordinateMass_nonneg
import Theorems.Thm_QuantumParallelRepetition_exactSourceAcceptedCoordinateMass_le_law

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (history : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    exactSourceAcceptedCoordinateMass G n S D
        (history.seed.coordinate, x, y, history) =
      if exactHistoryAccepted G n D history then
        (exactSeedWeight history.seed *
          exactFairWinningOutcomeBornMass
            G n S D history x y) /
          repeatedPostselectionMass G n S D
      else 0 := by
  classical
  by_cases accepted : exactHistoryAccepted G n D history
  · rw [if_pos accepted]
    unfold exactSourceAcceptedCoordinateMass
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single history.seed]
    · unfold exactFairWinningOutcomeBornMass
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro outcome _
      by_cases code :
          exactLocallySampleableCode D
            (history.seed, outcome) =
              (history.seed.coordinate, x, y, history)
      · by_cases winning :
          repeatedCoordinateWin G n history.seed.coordinate.val
            outcome = true
        · have same_history :
              exactHistoryCode D (history.seed, outcome) =
                history :=
            congrArg
              (fun t : ExactLocallySampleableTuple
                X Y A B D => t.2.2.2) code
          have conditioned :
              outcome ∈ FiniteEventLaw.winEvent
                (repeatedCoordinateWin G n) D := by
            apply (exactHistoryCode_accepted_iff
              G n D (history.seed, outcome)).mp
            rw [same_history]
            exact accepted
          simp [code, winning, exactPostselectedJointLaw,
            repeatedConditionedOutcomeLaw,
            conditionedEventDistribution,
            repeatedPostselectionMass, postselectionMass, conditioned]
          ring
        · simp [code, winning]
      · simp [code]
    · intro seed _ distinct
      apply Finset.sum_eq_zero
      intro outcome _
      have not_code :
          exactLocallySampleableCode D (seed, outcome) ≠
            (history.seed.coordinate, x, y, history) := by
        intro code
        have same := congrArg
          (fun t : ExactLocallySampleableTuple X Y A B D =>
            t.2.2.2.seed) code
        exact distinct same
      simp [not_code]
    · simp
  · rw [if_neg accepted]
    have law_zero :=
      exactLocallySampleableLaw_zero_of_not_accepted
        G n S D history.seed.coordinate x y history accepted
    exact le_antisymm
      (by
        simpa [law_zero] using
          exactSourceAcceptedCoordinateMass_le_law
            G n S D positive
            (history.seed.coordinate, x, y, history))
      (exactSourceAcceptedCoordinateMass_nonneg
        G n S D positive
        (history.seed.coordinate, x, y, history))
end QuantumParallelRepetition
