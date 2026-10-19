-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalMixedConjugateSelectedBranch_tensorAction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/82f38bcc-1a52-4f50-af82-6f5e0cd3641e

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
namespace QuantumParallelRepetition
theorem _root_.solution
    {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype τ] [DecidableEq τ]
    (U V : Matrix.unitaryGroup ι ℂ)
    (stage : EuclideanSpace ℂ (ι × ι))
    (work : EuclideanSpace ℂ τ) :
    unconditionalMixedConjugateSelectedBranchLocalAction
        U V
        (unconditionalMatchedVerifierTensor stage work) =
      unconditionalMatchedVerifierTensor
        (toLp 2
          ((((U : Matrix ι ι ℂ) ⊗ₖ
              (V : Matrix ι ι ℂ)).mulVec
            (ofLp stage)))) work := by
  classical
  ext ⟨⟨a, b⟩, t⟩
  simp [unconditionalMixedConjugateSelectedBranchLocalAction,
    unconditionalMixedConjugateSelectedBranchUnitary,
    unconditionalMatchedVerifierTensor,
    Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
    Matrix.one_apply,
    Fintype.sum_prod_type, Finset.sum_mul, mul_assoc]
end QuantumParallelRepetition
