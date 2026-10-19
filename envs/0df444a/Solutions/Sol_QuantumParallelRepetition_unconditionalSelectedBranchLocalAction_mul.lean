-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalSelectedBranchLocalAction_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/87fcfcca-1abe-41a8-b10a-3e8c6848ce0a

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
    {s t : Type*} [Fintype s] [DecidableEq s]
    [Fintype t] [DecidableEq t]
    (U₁ U₂ V₁ V₂ : Matrix.unitaryGroup s ℂ)
    (z : EuclideanSpace ℂ ((s × s) × t)) :
    unconditionalMixedConjugateSelectedBranchLocalAction
      (U₁ * U₂) (V₁ * V₂) z =
    unconditionalMixedConjugateSelectedBranchLocalAction U₁ V₁
      (unconditionalMixedConjugateSelectedBranchLocalAction
        U₂ V₂ z) := by
  classical
  simp [unconditionalMixedConjugateSelectedBranchLocalAction,
    unconditionalMixedConjugateSelectedBranchUnitary,
    Matrix.mulVec_mulVec, Matrix.mul_kronecker_mul]
  apply congrArg
    (fun (W : Matrix ((s × s) × t) ((s × s) × t) ℂ) =>
      W.mulVec (ofLp z))
  simpa using
    (Matrix.mul_kronecker_mul
      ((U₁ : Matrix s s ℂ) ⊗ₖ (V₁ : Matrix s s ℂ))
      ((U₂ : Matrix s s ℂ) ⊗ₖ (V₂ : Matrix s s ℂ))
      (1 : Matrix t t ℂ) (1 : Matrix t t ℂ))
end QuantumParallelRepetition
