-- Prove2me | solution 1 for QuantumParallelRepetition.exactRefinedPOVM_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/f818ff26-9ae7-4278-957e-11250384cc10

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_finiteLocalPurificationVector_quadratic
import Theorems.Thm_QuantumParallelRepetition_exactAliceRefinedPOVM_compression
import Theorems.Thm_QuantumParallelRepetition_exactBobRefinedPOVM_compression

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
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) (a : A) (b : B) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := ExactAliceLocalIndex G n S D r ×
          ExactBobLocalIndex G n S D r)
        (𝕜 := ℂ)
        (((exactAliceRefinedPOVM
          G n S D r a₀ x).effect a ⊗ₖ
          (1 : Matrix (S.Alice × S.Bob)
            (S.Alice × S.Bob) ℂ)) ⊗ₖ
          (exactBobRefinedPOVM
            G n S D r b₀ y).effect b))
      (exactUnnormalizedPsi G n S D r x y) =
      bornTracePairing S.state.matrix
        (exactAliceCoordinateFilter
          G n S D r.seed r.history r.aliceAnswer x a)
        (exactBobCoordinateFilter
          G n S D r.seed r.history r.bobAnswer y b) := by
  unfold exactUnnormalizedPsi
  rw [finiteLocalPurificationVector_quadratic,
    exactAliceRefinedPOVM_compression,
    exactBobRefinedPOVM_compression]
end QuantumParallelRepetition
