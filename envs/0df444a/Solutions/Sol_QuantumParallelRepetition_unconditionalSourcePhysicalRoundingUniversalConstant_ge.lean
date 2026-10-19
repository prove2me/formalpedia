-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalSourcePhysicalRoundingUniversalConstant_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/e0db4e80-6a4b-4c99-8fab-547f2c8175c2

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable
namespace QuantumParallelRepetition
theorem _root_.solution :
    128 ≤ unconditionalSourcePhysicalRoundingUniversalConstant := by
  unfold unconditionalSourcePhysicalRoundingUniversalConstant
  nlinarith [Real.sqrt_nonneg
    (34 + unconditionalPrefactorBucketCoefficient)]
end QuantumParallelRepetition
