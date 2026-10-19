-- Prove2me | solution 1 for QuantumParallelRepetition.exactSourceWinningEffect_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/c04489fc-1f8c-44bb-be8c-d41900a2d4f1

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_sourceHistoryQuadraticExpectation_matrix_sum
import Theorems.Thm_QuantumParallelRepetition_exactSourceJointEffect_quadratic

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
    (a₀ : A) (b₀ : B) (x : X) (y : Y) :
    quadraticExpectation
      (exactSourceWinningEffectCLM
        G n S D r a₀ b₀ x y)
      (exactUnnormalizedPsi G n S D r x y) =
      ∑ a : A, ∑ b : B,
        if G.predicate x y a b = true then
          bornTracePairing S.state.matrix
            (exactAliceCoordinateFilter
              G n S D r.seed r.history r.aliceAnswer x a)
            (exactBobCoordinateFilter
              G n S D r.seed r.history r.bobAnswer y b)
        else 0 := by
  classical
  unfold exactSourceWinningEffectCLM
    exactSourceWinningEffect
  rw [sourceHistoryQuadraticExpectation_matrix_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [sourceHistoryQuadraticExpectation_matrix_sum]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · exact exactSourceJointEffect_quadratic
      G n S D r a₀ b₀ x y a b
  · simp [quadraticExpectation]
end QuantumParallelRepetition
