-- Prove2me | solution 1 for QuantumParallelRepetition.exactAliceCoordinateFilter_eq_joint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/727d2e4e-15d3-4a42-922c-5fe5caa116d9

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
set_option maxHeartbeats 1800000
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
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) (y : Y) (a : A)
    (nonzero : exactFiberQuestionMass
      G n D seed history x y ≠ 0) :
    exactAliceCoordinateFilter
        G n S D seed history answer x a =
      exactJointAliceCoordinateFilter
        G n S D seed history answer x y a := by
  exact exactAliceConditionalMatrix_eq_joint
    G n D seed history x y nonzero
    (fun xs => conditionedAliceCoordinateEffect
      G n S D answer xs seed.coordinate.val a)
end QuantumParallelRepetition
