-- Prove2me | solution 1 for QuantumParallelRepetition.convexMixtureStrategy_outcomeProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/bf1276be-c511-46dc-8934-3f9e2d830a29

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_mixtureJointEffect_compress
import Theorems.Thm_QuantumParallelRepetition_mixtureEmbedding_trace_mul
import Theorems.Thm_QuantumParallelRepetition_mixtureBlockMatrix_trace_mul

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
variable {X Y A B : Type*} {J : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype J] [DecidableEq J]
variable {G : Game X Y A B}
namespace QuantumParallelRepetition
theorem _root_.solution
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (h_normalized : (∑ j : J, p j) = 1)
    (S : J → Strategy G) (x : X) (y : Y) (a : A) (b : B) :
    (convexMixtureStrategy p hp h_normalized S).outcomeProbability
        x y a b =
      ∑ j : J, p j * (S j).outcomeProbability x y a b := by
  change
    (Matrix.trace
      ((mixtureEmbedding S * mixtureBlockMatrix p S *
          (mixtureEmbedding S)ᴴ) *
        ((mixtureAlicePOVM S x).effect a ⊗ₖ
          (mixtureBobPOVM S y).effect b))).re = _
  rw [mixtureEmbedding_trace_mul, mixtureJointEffect_compress,
    mixtureBlockMatrix_trace_mul]
  simp [Strategy.outcomeProbability]
end QuantumParallelRepetition
