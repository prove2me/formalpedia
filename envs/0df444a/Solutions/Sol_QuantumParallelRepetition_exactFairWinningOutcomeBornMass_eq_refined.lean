-- Prove2me | solution 1 for QuantumParallelRepetition.exactFairWinningOutcomeBornMass_eq_refined
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/da4b4a14-f6a5-4bbd-98b2-7e176b3ed0cf

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_exactFineCoordinateWinningBorn_collapse

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
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (history : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    exactFairWinningOutcomeBornMass
      G n S D history x y =
        exactFairCoordinateRefinedWinningBornMass
          G n S D history x y := by
  classical
  unfold exactFairWinningOutcomeBornMass
    exactFairCoordinateRefinedWinningBornMass
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro xs _
  apply Finset.sum_congr rfl
  intro ys _
  have compatibility :
      (exactAliceQuestionCompatible
        D history.seed history.history x xs ∧
       exactBobQuestionCompatible
        D history.seed history.history y ys) ↔
      exactRevealCode D history.seed (xs, ys) = history.history ∧
        xs history.seed.coordinate.val = x ∧
        ys history.seed.coordinate.val = y :=
    (exactRevealCode_compatible_iff
      D history.seed history.history x y xs ys).symm
  by_cases compatible :
      exactAliceQuestionCompatible
        D history.seed history.history x xs ∧
      exactBobQuestionCompatible
        D history.seed history.history y ys
  · have actual := compatibility.mp compatible
    rw [exactFiberQuestionWeight, if_pos compatible,
      exactFineCoordinateWinningBorn_collapse
        G n S D history.aliceAnswer history.bobAnswer xs ys
        history.seed.coordinate.val x y]
    calc
      (∑ aa : Fin n → A, ∑ bb : Fin n → B,
        if exactLocallySampleableCode D
            (history.seed, (xs, ys, aa, bb)) =
            (history.seed.coordinate, x, y, history) ∧
          repeatedCoordinateWin G n history.seed.coordinate.val
            (xs, ys, aa, bb) = true
        then (strategyEventLaw (G.repeat n) S).weight
          (xs, ys, aa, bb)
        else 0) =
        ∑ aa : Fin n → A, ∑ bb : Fin n → B,
          (G.repeat n).questionWeight xs ys *
            if
              (∀ (j : Fin n) (member : j ∈ D),
                aa j = history.aliceAnswer ⟨j, member⟩) ∧
              (∀ (j : Fin n) (member : j ∈ D),
                bb j = history.bobAnswer ⟨j, member⟩) ∧
              G.predicate x y
                (aa history.seed.coordinate.val)
                (bb history.seed.coordinate.val) = true
            then S.outcomeProbability xs ys aa bb
            else 0 := by
          apply Finset.sum_congr rfl
          intro aa _
          apply Finset.sum_congr rfl
          intro bb _
          have fiber :=
            exactLocallySampleableCode_fixedSeed_fiber_iff
              D history x y (xs, ys, aa, bb)
          have event :
              (exactLocallySampleableCode D
                  (history.seed, (xs, ys, aa, bb)) =
                    (history.seed.coordinate, x, y, history) ∧
                repeatedCoordinateWin G n history.seed.coordinate.val
                  (xs, ys, aa, bb) = true) ↔
              ((∀ (j : Fin n) (member : j ∈ D),
                aa j = history.aliceAnswer ⟨j, member⟩) ∧
               (∀ (j : Fin n) (member : j ∈ D),
                bb j = history.bobAnswer ⟨j, member⟩) ∧
               G.predicate x y
                (aa history.seed.coordinate.val)
                (bb history.seed.coordinate.val) = true) := by
            rw [fiber]
            simp [actual.1, actual.2.1, actual.2.2,
              repeatedCoordinateWin, and_assoc]
          by_cases wins :
              (∀ (j : Fin n) (member : j ∈ D),
                aa j = history.aliceAnswer ⟨j, member⟩) ∧
              (∀ (j : Fin n) (member : j ∈ D),
                bb j = history.bobAnswer ⟨j, member⟩) ∧
              G.predicate x y
                (aa history.seed.coordinate.val)
                (bb history.seed.coordinate.val) = true
          · have selected := event.mpr wins
            rw [if_pos selected, if_pos wins]
            rfl
          · have rejected :
              ¬ (exactLocallySampleableCode D
                    (history.seed, (xs, ys, aa, bb)) =
                  (history.seed.coordinate, x, y, history) ∧
                repeatedCoordinateWin G n history.seed.coordinate.val
                  (xs, ys, aa, bb) = true) := by
              intro selected
              exact wins (event.mp selected)
            rw [if_neg rejected, if_neg wins]
            simp
      _ = (G.repeat n).questionWeight xs ys *
        (∑ aa : Fin n → A, ∑ bb : Fin n → B,
          if
            (∀ (j : Fin n) (member : j ∈ D),
              aa j = history.aliceAnswer ⟨j, member⟩) ∧
            (∀ (j : Fin n) (member : j ∈ D),
              bb j = history.bobAnswer ⟨j, member⟩) ∧
            G.predicate x y
              (aa history.seed.coordinate.val)
              (bb history.seed.coordinate.val) = true
          then S.outcomeProbability xs ys aa bb
          else 0) := by
          simp only [Finset.mul_sum]
  · rw [exactFiberQuestionWeight, if_neg compatible,
      zero_mul]
    apply Finset.sum_eq_zero
    intro aa _
    apply Finset.sum_eq_zero
    intro bb _
    have no_code :
        exactLocallySampleableCode D
          (history.seed, (xs, ys, aa, bb)) ≠
            (history.seed.coordinate, x, y, history) := by
      intro code
      have conditions :=
        (exactLocallySampleableCode_fixedSeed_fiber_iff
          D history x y (xs, ys, aa, bb)).mp code
      exact compatible
        (compatibility.mpr
          ⟨conditions.1, conditions.2.1, conditions.2.2.1⟩)
    simp [no_code]
end QuantumParallelRepetition
