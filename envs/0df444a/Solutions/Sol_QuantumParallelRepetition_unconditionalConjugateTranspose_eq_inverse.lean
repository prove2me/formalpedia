-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalConjugateTranspose_eq_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/6429c563-7b8e-42e9-8f76-3e5108f3d3b2

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
namespace QuantumParallelRepetition
theorem _root_.solution
    {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (conjugateUnitary U : Matrix (Fin d) (Fin d) ℂ).transpose =
      ((U⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) :
        Matrix (Fin d) (Fin d) ℂ) := by
  change U.val.conjTranspose.transpose.transpose =
    ((U⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) :
      Matrix (Fin d) (Fin d) ℂ)
  rw [Matrix.transpose_transpose]
  change star (U : Matrix (Fin d) (Fin d) ℂ) = _
  exact congrArg
    (fun V : Matrix.unitaryGroup (Fin d) ℂ =>
      (V : Matrix (Fin d) (Fin d) ℂ))
    (Unitary.star_eq_inv U)
end QuantumParallelRepetition
