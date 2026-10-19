-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalMatchedVerifierEffect_tensor_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/a2eb7364-2912-4d00-9d8d-5283435e26e0

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
    {s t : Type*} [Fintype s] [Fintype t]
    [DecidableEq s] [DecidableEq t]
    (effect : Matrix s s ℂ)
    (positive : effect.PosSemidef) :
    (effect ⊗ₖ (1 : Matrix t t ℂ)).PosSemidef :=
  positive.kronecker Matrix.PosSemidef.one
end QuantumParallelRepetition
