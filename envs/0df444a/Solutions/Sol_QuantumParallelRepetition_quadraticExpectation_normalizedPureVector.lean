-- Prove2me | solution 1 for QuantumParallelRepetition.quadraticExpectation_normalizedPureVector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/538fae12-64ac-478b-a0b1-ff05d73e38af

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
namespace QuantumParallelRepetition
theorem _root_.solution
    {d : Type*} [Fintype d]
    (W : EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d)
    (z : EuclideanSpace ℂ d) :
    quadraticExpectation W (normalizedPureVector z) =
      quadraticExpectation W z / ‖z‖ ^ 2 := by
  unfold quadraticExpectation normalizedPureVector
  rw [map_smul, inner_smul_left, inner_smul_right]
  simp [Complex.mul_re, div_eq_mul_inv, pow_two]
  by_cases hz : ‖z‖ = 0
  · simp [hz]
  · field_simp
end QuantumParallelRepetition
