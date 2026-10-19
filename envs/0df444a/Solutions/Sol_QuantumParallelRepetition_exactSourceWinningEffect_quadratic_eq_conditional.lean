-- Prove2me | solution 1 for QuantumParallelRepetition.exactSourceWinningEffect_quadratic_eq_conditional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/7d594684-d6e8-4438-a0e5-37308e6fef3e

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_exactAliceCoordinateFilter_eq_joint
import Theorems.Thm_QuantumParallelRepetition_exactBobCoordinateFilter_eq_joint
import Theorems.Thm_QuantumParallelRepetition_exactSourceWinningEffect_quadratic

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
    (a₀ : A) (b₀ : B) (x : X) (y : Y)
    (supported : exactFiberQuestionMass
      G n D r.seed r.history x y ≠ 0) :
    quadraticExpectation
      (exactSourceWinningEffectCLM
        G n S D r a₀ b₀ x y)
      (exactUnnormalizedPsi G n S D r x y) =
      exactJointConditionalWinningMass
        G n S D r.seed r.history r.aliceAnswer r.bobAnswer x y := by
  rw [exactSourceWinningEffect_quadratic]
  unfold exactJointConditionalWinningMass
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · rw [exactAliceCoordinateFilter_eq_joint
      G n S D r.seed r.history r.aliceAnswer x y a supported,
      exactBobCoordinateFilter_eq_joint
        G n S D r.seed r.history r.bobAnswer x y b supported]
  · rfl
end QuantumParallelRepetition
