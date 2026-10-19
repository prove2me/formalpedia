-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalMatchedVerifierTensor_sub_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/9b6e4d86-9c52-429b-ac7c-414d4d77ff19

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
theorem _root_.solution
    {s t : Type*} [Fintype s] [Fintype t]
    (x y : EuclideanSpace ℂ s)
    (work : EuclideanSpace ℂ t) :
    unconditionalMatchedVerifierTensor x work -
      unconditionalMatchedVerifierTensor y work =
        unconditionalMatchedVerifierTensor (x - y) work := by
  ext q
  change x q.1 * work q.2 - y q.1 * work q.2 =
    (x q.1 - y q.1) * work q.2
  ring
end QuantumParallelRepetition
