-- Prove2me | solution 1 for QuantumParallelRepetition.exactAliceRefinedPOVM_compression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/2d9e4a27-fcd1-42ef-b628-71ace16673c0

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_purifiedRefinedPOVM_compression

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
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (x : X) (a : A) :
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inl x)).conjTranspose *
      (exactAliceRefinedPOVM G n S D r a₀ x).effect a *
      exactAlicePurificationMatrix
        G n S D r.seed r.history r.aliceAnswer (.inl x) =
      exactAliceCoordinateFilter
        G n S D r.seed r.history r.aliceAnswer x a := by
  exact purifiedRefinedPOVM_compression
    (exactAliceQuestionFilter
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAliceQuestionFilter_posSemidef
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inl x))
    (exactAliceQuestionPurificationMatrix_gram G n S D r x)
    (exactAliceCoordinateFilter
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAliceCoordinateFilter_posSemidef
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAliceCoordinateFilter_sum
      G n S D r.seed r.history r.aliceAnswer x)
    a₀ a
end QuantumParallelRepetition
