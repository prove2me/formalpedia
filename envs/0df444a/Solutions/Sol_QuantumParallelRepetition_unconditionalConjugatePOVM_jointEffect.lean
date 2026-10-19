-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalConjugatePOVM_jointEffect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/a0d69ea7-b6ef-4479-a906-a13f1db43486

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
    {A B ι κ : Type*} [Fintype A] [Fintype B]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : POVM A ι) (Q : POVM B κ) (a : A) (b : B) :
    (unconditionalConjugatePOVM P).effect a ⊗ₖ
        (unconditionalConjugatePOVM Q).effect b =
      (P.effect a ⊗ₖ Q.effect b).transpose := by
  exact Matrix.kroneckerMap_transpose (fun x y : ℂ => x * y)
    (P.effect a) (Q.effect b)
end QuantumParallelRepetition
