-- Prove2me | solution 1 for QuantumParallelRepetition.exactSourceGlobalJointBasis_vector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/10b1c883-d7b4-45c3-aa01-2b2e6bb74703

import Mathlib
import Definitions.Def_QuantumParallelRepetition

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
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (z : EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r))
    (i : ExactAliceLocalIndex G n S D r ×
      ExactBobLocalIndex G n S D r) :
    exactGlobalHistoryVector G n S D r
        (exactPaddedVector G n S D r z)
        (exactSourceGlobalJointBasis G n S D r i) =
      z i := by
  rcases i with ⟨ia, ib⟩
  change
    (if ha : r = r then
      if hb : r = r then
        exactPaddedVector G n S D r z
          (ha ▸ Sum.inr (Sum.inl ia),
            hb ▸ Sum.inr (Sum.inr ib))
      else 0
    else 0) = z (ia, ib)
  simp only [exactPaddedVector, dite_true]
end QuantumParallelRepetition
