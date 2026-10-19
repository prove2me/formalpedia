-- Prove2me | solution 1 for QuantumParallelRepetition.exactSourceJointEffect_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/378d8116-46ce-40cb-9b72-234dd941202e

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_exactRefinedPOVM_quadratic

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) (a : A) (b : B) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := ExactAliceLocalIndex G n S D r ×
          ExactBobLocalIndex G n S D r) (𝕜 := ℂ)
        (exactSourceJointEffect G n S D r a₀ b₀ x y a b))
      (exactUnnormalizedPsi G n S D r x y) =
      bornTracePairing S.state.matrix
        (exactAliceCoordinateFilter
          G n S D r.seed r.history r.aliceAnswer x a)
        (exactBobCoordinateFilter
          G n S D r.seed r.history r.bobAnswer y b) := by
  classical
  simpa [exactSourceJointEffect,
    exactSourceAliceRefinedPOVM,
    exactSourceBobRefinedPOVM, purificationAlicePOVM] using
    (exactRefinedPOVM_quadratic
      G n S D r a₀ b₀ x y a b)
end QuantumParallelRepetition
