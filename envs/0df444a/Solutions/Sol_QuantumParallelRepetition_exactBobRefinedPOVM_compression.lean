-- Prove2me | solution 1 for QuantumParallelRepetition.exactBobRefinedPOVM_compression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/ee25ec15-545b-45ef-89d1-0481e0a7f0af

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
    [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (b₀ : B) (y : Y) (b : B) :
    (exactBobPurificationMatrix
      G n S D r.seed r.history r.bobAnswer (.inl y)).conjTranspose *
      (exactBobRefinedPOVM G n S D r b₀ y).effect b *
      exactBobPurificationMatrix
        G n S D r.seed r.history r.bobAnswer (.inl y) =
      exactBobCoordinateFilter
        G n S D r.seed r.history r.bobAnswer y b := by
  exact purifiedRefinedPOVM_compression
    (exactBobQuestionFilter
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobQuestionFilter_posSemidef
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobPurificationMatrix
      G n S D r.seed r.history r.bobAnswer (.inl y))
    (exactBobQuestionPurificationMatrix_gram G n S D r y)
    (exactBobCoordinateFilter
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobCoordinateFilter_posSemidef
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobCoordinateFilter_sum
      G n S D r.seed r.history r.bobAnswer y)
    b₀ b
end QuantumParallelRepetition
