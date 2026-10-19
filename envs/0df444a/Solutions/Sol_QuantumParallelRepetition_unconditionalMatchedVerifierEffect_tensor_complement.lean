-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalMatchedVerifierEffect_tensor_complement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/31da110d-0bb7-4bc1-ab43-01e85e384180

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
    (effect : Matrix s s ℂ) :
    (1 : Matrix (s × t) (s × t) ℂ) -
        (effect ⊗ₖ (1 : Matrix t t ℂ)) =
      (1 - effect) ⊗ₖ (1 : Matrix t t ℂ) := by
  classical
  ext ⟨i, k⟩ ⟨j, l⟩
  by_cases same_target : i = j
  · subst j
    by_cases same_work : k = l
    · subst l
      simp [Matrix.kroneckerMap_apply]
    · simp [Matrix.kroneckerMap_apply, same_work]
  · by_cases same_work : k = l
    · subst l
      simp [Matrix.kroneckerMap_apply, same_target]
    · simp [Matrix.kroneckerMap_apply, same_target, same_work]
end QuantumParallelRepetition
