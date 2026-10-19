-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalConjugatePureVector_sub_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/6a9d0367-742b-4a31-ad28-3a14e59188d0

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalConjugatePureVector_norm

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
    {ι : Type*} [Fintype ι]
    (x y : EuclideanSpace ℂ ι) :
    ‖unconditionalConjugatePureVector x -
      unconditionalConjugatePureVector y‖ = ‖x - y‖ := by
  have conjugate_sub :
      unconditionalConjugatePureVector x -
          unconditionalConjugatePureVector y =
        unconditionalConjugatePureVector (x - y) := by
    ext i
    simp [unconditionalConjugatePureVector, star_sub]
  rw [conjugate_sub, unconditionalConjugatePureVector_norm]
end QuantumParallelRepetition
