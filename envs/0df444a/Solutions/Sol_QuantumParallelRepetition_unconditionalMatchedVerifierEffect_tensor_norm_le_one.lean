-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalMatchedVerifierEffect_tensor_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/4835755e-6915-4d10-b829-f6c8d03210a2

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_matrixEffectCLM_norm_le_one
import Theorems.Thm_QuantumParallelRepetition_unconditionalMatchedVerifierEffect_tensor_posSemidef
import Theorems.Thm_QuantumParallelRepetition_unconditionalMatchedVerifierEffect_tensor_complement_posSemidef

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
    (positive : effect.PosSemidef)
    (complement : (1 - effect).PosSemidef) :
    ‖Matrix.toEuclideanCLM (n := s × t) (𝕜 := ℂ)
        (effect ⊗ₖ (1 : Matrix t t ℂ))‖ ≤ 1 := by
  exact matrixEffectCLM_norm_le_one
    (effect ⊗ₖ (1 : Matrix t t ℂ))
    (unconditionalMatchedVerifierEffect_tensor_posSemidef
      effect positive)
    (unconditionalMatchedVerifierEffect_tensor_complement_posSemidef
      effect complement)
end QuantumParallelRepetition
