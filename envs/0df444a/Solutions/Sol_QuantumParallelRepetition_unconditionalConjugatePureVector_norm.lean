-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalConjugatePureVector_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/0d57cf79-fe13-4c34-b56b-32c227bffd82

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalConjugatePureVector_norm_sq

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
    {ι : Type*} [Fintype ι] (z : EuclideanSpace ℂ ι) :
    ‖unconditionalConjugatePureVector z‖ = ‖z‖ := by
  have squares := unconditionalConjugatePureVector_norm_sq z
  nlinarith [norm_nonneg (unconditionalConjugatePureVector z),
    norm_nonneg z]
end QuantumParallelRepetition
