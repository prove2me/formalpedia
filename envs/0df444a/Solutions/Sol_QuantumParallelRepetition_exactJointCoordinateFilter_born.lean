-- Prove2me | solution 1 for QuantumParallelRepetition.exactJointCoordinateFilter_born
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/faeb8d51-e83a-48ef-9285-46ef978bcbde

import Mathlib
import Definitions.Def_QuantumParallelRepetition

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
    (x : X) (y : Y) (a : A) (b : B)
    (nonzero : exactFiberQuestionMass
      G n D seed history x y ≠ 0) :
    bornTracePairing S.state.matrix
        (exactJointAliceCoordinateFilter
          G n S D seed history aliceAnswer x y a)
        (exactJointBobCoordinateFilter
          G n S D seed history bobAnswer x y b) =
      ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
        exactConditionalQuestionWeight
          G n D seed history x y xs ys *
        bornTracePairing S.state.matrix
          (conditionedAliceCoordinateEffect
            G n S D aliceAnswer xs seed.coordinate.val a)
          (conditionedBobCoordinateEffect
            G n S D bobAnswer ys seed.coordinate.val b) := by
  exact exactFiber_born_of_rank_one
    G n S D seed history x y nonzero
    (fun xs => conditionedAliceCoordinateEffect
      G n S D aliceAnswer xs seed.coordinate.val a)
    (fun ys => conditionedBobCoordinateEffect
      G n S D bobAnswer ys seed.coordinate.val b)
end QuantumParallelRepetition
