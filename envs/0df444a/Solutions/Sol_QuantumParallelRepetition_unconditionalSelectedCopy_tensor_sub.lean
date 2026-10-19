-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalSelectedCopy_tensor_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/cd910a75-be46-4bfc-a83b-7224a43a6e0f

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
    {s τ : Type*} [Fintype s] [Fintype τ]
    (x y : EuclideanSpace ℂ s) (work : EuclideanSpace ℂ τ) :
    unconditionalMatchedVerifierTensor x work -
        unconditionalMatchedVerifierTensor y work =
      unconditionalMatchedVerifierTensor (x - y) work := by
  ext ⟨i, j⟩
  change x i * work j - y i * work j =
    (x i - y i) * work j
  ring
end QuantumParallelRepetition
