-- Prove2me | solution 1 for QuantumParallelRepetition.exactPsi_eq_padded_normalizedPureVector_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/2f33065c-6a84-4614-ab07-973db54f5f6e

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
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y)
    (nonzero : exactUnnormalizedPsi G n S D r x y ≠ 0) :
    exactPsi G n S D r x y =
      exactPaddedVector G n S D r
        (normalizedPureVector
          (exactUnnormalizedPsi G n S D r x y)) := by
  classical
  let raw := exactUnnormalizedPsi G n S D r x y
  have padded_nonzero :
      exactPaddedVector G n S D r raw ≠ 0 := by
    intro zero
    apply nonzero
    apply norm_eq_zero.mp
    rw [← exactPaddedVector_norm G n S D r raw, zero]
    exact norm_zero
  unfold exactPsi normalizeOrDefault
  rw [if_neg padded_nonzero, NormedSpace.normalize,
    exactPaddedVector_norm]
  ext q
  rcases q with ⟨i, j⟩
  rcases i with i | (i | i) <;>
    rcases j with j | (j | j) <;>
    simp [exactPaddedVector, normalizedPureVector,
      smul_eq_mul]
end QuantumParallelRepetition
