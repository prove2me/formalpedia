-- Prove2me | solution 1 for QuantumParallelRepetition.exactSourceGlobalWinningEffect_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/65650163-910b-4aec-b511-6bdb5e5a345d

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_matrixQuadraticExpectation_injective
import Theorems.Thm_QuantumParallelRepetition_exactSourceGlobalJointBasis_injective
import Theorems.Thm_QuantumParallelRepetition_exactSourceGlobalJointBasis_vector
import Theorems.Thm_QuantumParallelRepetition_exactSourceGlobalJointBasis_support
import Theorems.Thm_QuantumParallelRepetition_exactSourceGlobalWinningEffect_compression

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y)
    (z : EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r)) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := ExactGlobalHistoryLocalIndex G n S D ×
          ExactGlobalHistoryLocalIndex G n S D)
        (𝕜 := ℂ)
        (exactSourceGlobalWinningEffect G n S D a₀ b₀ x y))
      (exactGlobalHistoryVector G n S D r
        (exactPaddedVector G n S D r z)) =
      quadraticExpectation
        (exactSourceWinningEffectCLM G n S D r a₀ b₀ x y)
        z := by
  classical
  unfold exactSourceWinningEffectCLM
  apply matrixQuadraticExpectation_injective
    (exactSourceGlobalJointBasis G n S D r)
    (exactSourceGlobalJointBasis_injective G n S D r)
  · exact exactSourceGlobalJointBasis_vector G n S D r z
  · exact exactSourceGlobalJointBasis_support G n S D r z
  · exact exactSourceGlobalWinningEffect_compression
      G n S D r a₀ b₀ x y
end QuantumParallelRepetition
