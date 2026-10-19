-- Prove2me | solution 1 for QuantumParallelRepetition.rectangular_matrix_quadratic_compression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/074bef73-3376-4c90-8eb4-80656b8269d6

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
namespace QuantumParallelRepetition
theorem _root_.solution
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (K : Matrix e d ℂ) (E : Matrix e e ℂ)
    (z : EuclideanSpace ℂ d) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := e) (𝕜 := ℂ) E)
      (toLp 2 (K.mulVec (ofLp z))) =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)
          (K.conjTranspose * E * K)) z := by
  unfold quadraticExpectation
  rw [EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct]
  change
    (E.mulVec (K.mulVec (ofLp z)) ⬝ᵥ
      star (K.mulVec (ofLp z))).re =
    ((K.conjTranspose * E * K).mulVec (ofLp z) ⬝ᵥ
      star (ofLp z)).re
  rw [dotProduct_comm (E.mulVec (K.mulVec (ofLp z))),
    Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]
  rw [dotProduct_comm]
end QuantumParallelRepetition
