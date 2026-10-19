-- Prove2me | solution 1 for QuantumParallelRepetition.unitaryConjugatePOVM_jointEffect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/a36cd5c5-946f-4ddc-b562-8a46f313f71d

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
namespace QuantumParallelRepetition
theorem _root_.solution
    {A B d : Type} [Fintype A] [Fintype B]
    [Fintype d] [DecidableEq d]
    (U V : Matrix.unitaryGroup d ℂ)
    (P : POVM A d) (Q : POVM B d)
    (a : A) (b : B) :
    (unitaryConjugatePOVM U P).effect a ⊗ₖ
      (unitaryConjugatePOVM V Q).effect b =
      (((U : Matrix d d ℂ) ⊗ₖ (V : Matrix d d ℂ))ᴴ *
        (P.effect a ⊗ₖ Q.effect b) *
        ((U : Matrix d d ℂ) ⊗ₖ (V : Matrix d d ℂ))) := by
  change
    (((U : Matrix d d ℂ)ᴴ * P.effect a * (U : Matrix d d ℂ)) ⊗ₖ
      ((V : Matrix d d ℂ)ᴴ * Q.effect b * (V : Matrix d d ℂ))) =
      (((U : Matrix d d ℂ) ⊗ₖ (V : Matrix d d ℂ))ᴴ *
        (P.effect a ⊗ₖ Q.effect b) *
        ((U : Matrix d d ℂ) ⊗ₖ (V : Matrix d d ℂ)))
  rw [Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]
end QuantumParallelRepetition
