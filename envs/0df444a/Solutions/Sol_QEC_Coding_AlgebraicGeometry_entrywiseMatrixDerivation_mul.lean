-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:42:14.881648+00:00
-- url     : https://prove2.me/submissions/1e4a9936-6a98-44ea-bc89-671a46816c39

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_MatrixDerivation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_add

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution {m n p : Type*} [Fintype n]
    (D : Derivation k K K) (A : Matrix m n K) (B : Matrix n p K) :
    entrywiseMatrixDerivation D (A * B) =
      entrywiseMatrixDerivation D A * B +
        A * entrywiseMatrixDerivation D B := by
  ext i j
  simp only [entrywiseMatrixDerivation_apply, Matrix.mul_apply, map_sum,
    D.leibniz, smul_eq_mul, Matrix.add_apply]
  rw [Finset.sum_add_distrib]
  have hcomm :
      (∑ x, B x j * D (A i x)) = ∑ x, D (A i x) * B x j := by
    apply Finset.sum_congr rfl
    intro x _
    rw [mul_comm]
  rw [hcomm, add_comm]
end QEC.Coding.AlgebraicGeometry
