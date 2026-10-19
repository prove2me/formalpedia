-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualSelectedBranchLocalAction_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/002b0a78-b4f0-4603-84ce-444fbbab435e

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
    {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype τ] [DecidableEq τ]
    (U V : Matrix.unitaryGroup ι ℂ)
    (x y : EuclideanSpace ℂ ((ι × ι) × τ)) :
    unconditionalMixedConjugateSelectedBranchLocalAction U V x -
        unconditionalMixedConjugateSelectedBranchLocalAction U V y =
      unconditionalMixedConjugateSelectedBranchLocalAction
        U V (x - y) := by
  classical
  ext i
  simp [unconditionalMixedConjugateSelectedBranchLocalAction,
    Matrix.mulVec, dotProduct, Finset.sum_sub_distrib, mul_sub]
end QuantumParallelRepetition
