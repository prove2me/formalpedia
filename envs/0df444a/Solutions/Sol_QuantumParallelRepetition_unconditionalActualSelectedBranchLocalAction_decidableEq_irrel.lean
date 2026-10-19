-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualSelectedBranchLocalAction_decidableEq_irrel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/3a817609-8a6c-418d-8c7d-2d0336c24a9a

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
    {ι τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ]
    (left right : DecidableEq τ)
    (U V : Matrix.unitaryGroup ι ℂ)
    (z : EuclideanSpace ℂ ((ι × ι) × τ)) :
    @unconditionalMixedConjugateSelectedBranchLocalAction
      ι τ inferInstance inferInstance inferInstance left U V z =
    @unconditionalMixedConjugateSelectedBranchLocalAction
      ι τ inferInstance inferInstance inferInstance right U V z := by
  have same : left = right := Subsingleton.elim left right
  cases same
  rfl
end QuantumParallelRepetition
