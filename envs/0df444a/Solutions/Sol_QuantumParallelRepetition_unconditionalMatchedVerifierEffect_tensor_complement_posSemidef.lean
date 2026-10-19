-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalMatchedVerifierEffect_tensor_complement_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/d6f8ce56-fac9-4cf7-8b80-bedb97a63fbd

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalMatchedVerifierEffect_tensor_complement

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
    (complement : (1 - effect).PosSemidef) :
    ((1 : Matrix (s × t) (s × t) ℂ) -
      (effect ⊗ₖ (1 : Matrix t t ℂ))).PosSemidef := by
  rw [unconditionalMatchedVerifierEffect_tensor_complement]
  exact complement.kronecker Matrix.PosSemidef.one
end QuantumParallelRepetition
