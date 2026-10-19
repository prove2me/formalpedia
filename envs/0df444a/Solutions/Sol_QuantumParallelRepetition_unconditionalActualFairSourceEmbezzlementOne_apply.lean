-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairSourceEmbezzlementOne_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/88fba997-1963-4c08-8c86-9ea1cafe0507

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
namespace QuantumParallelRepetition
theorem _root_.solution :
    embezzlementState 1 (0, 0) = 1 := by
  simp [embezzlementState, rawEmbezzlementState,
    EuclideanSpace.norm_eq, Fintype.sum_prod_type]
end QuantumParallelRepetition
