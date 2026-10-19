-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalConjugateBobBasisOverlapCancellation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/f7e7c8fa-7ee2-414d-9553-0d39dfe11c24

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalConjugateTranspose_eq_inverse

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
    {d : ℕ} (U V : Matrix.unitaryGroup (Fin d) ℂ) :
    (unitaryBasisOverlap U V : Matrix (Fin d) (Fin d) ℂ) *
        (conjugateUnitary V :
          Matrix (Fin d) (Fin d) ℂ).transpose =
      (conjugateUnitary U :
        Matrix (Fin d) (Fin d) ℂ).transpose := by
  rw [unconditionalConjugateTranspose_eq_inverse,
    unconditionalConjugateTranspose_eq_inverse]
  change
    (((U⁻¹ * V : Matrix.unitaryGroup (Fin d) ℂ) :
      Matrix (Fin d) (Fin d) ℂ)) *
      ((V⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) :
        Matrix (Fin d) (Fin d) ℂ) =
      ((U⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) :
        Matrix (Fin d) (Fin d) ℂ)
  change
    (((U⁻¹ * V) * V⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) :
      Matrix (Fin d) (Fin d) ℂ) =
      ((U⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) :
        Matrix (Fin d) (Fin d) ℂ)
  simp
end QuantumParallelRepetition
