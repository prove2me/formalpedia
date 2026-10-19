-- Prove2me | solution 1 for QuantumParallelRepetition.exactJointConditionalWinningMass_born
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/08197697-2a7d-4a63-b77e-f17ff48b2dc0

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_exactJointCoordinateFilter_born

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (aliceAnswer : {j : Fin n // j ∈ D} → A)
    (bobAnswer : {j : Fin n // j ∈ D} → B)
    (x : X) (y : Y)
    (nonzero : exactFiberQuestionMass
      G n D seed history x y ≠ 0) :
    exactJointConditionalWinningMass
        G n S D seed history aliceAnswer bobAnswer x y =
      ∑ a : A, ∑ b : B,
        if G.predicate x y a b = true then
          ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
            exactConditionalQuestionWeight
              G n D seed history x y xs ys *
            bornTracePairing S.state.matrix
              (conditionedAliceCoordinateEffect
                G n S D aliceAnswer xs seed.coordinate.val a)
              (conditionedBobCoordinateEffect
                G n S D bobAnswer ys seed.coordinate.val b)
        else 0 := by
  classical
  unfold exactJointConditionalWinningMass
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · exact exactJointCoordinateFilter_born
      G n S D seed history aliceAnswer bobAnswer x y a b nonzero
  · rfl
end QuantumParallelRepetition
