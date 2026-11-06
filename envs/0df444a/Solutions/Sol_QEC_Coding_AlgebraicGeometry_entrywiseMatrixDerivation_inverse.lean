-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:28:44.906206+00:00
-- url     : https://prove2.me/submissions/33b6437d-c57a-4f2a-bbcd-1670b06f99e4

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_MatrixDerivation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_mul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_one

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution {n : Type*} [Fintype n]
    [DecidableEq n] (D : Derivation k K K) (A U : Matrix n n K)
    (hAU : A * U = 1) (hUA : U * A = 1) :
    entrywiseMatrixDerivation D U =
      -(U * entrywiseMatrixDerivation D A * U) := by
  have hzero :
      entrywiseMatrixDerivation D A * U +
          A * entrywiseMatrixDerivation D U = 0 := by
    calc
      _ = entrywiseMatrixDerivation D (A * U) :=
        (entrywiseMatrixDerivation_mul D A U).symm
      _ = entrywiseMatrixDerivation D 1 := by rw [hAU]
      _ = 0 := entrywiseMatrixDerivation_one D
  have hright :
      A * entrywiseMatrixDerivation D U =
        -(entrywiseMatrixDerivation D A * U) :=
    eq_neg_of_add_eq_zero_right hzero
  calc
    entrywiseMatrixDerivation D U = 1 * entrywiseMatrixDerivation D U :=
      (one_mul _).symm
    _ = (U * A) * entrywiseMatrixDerivation D U := by rw [hUA]
    _ = U * (A * entrywiseMatrixDerivation D U) := by rw [Matrix.mul_assoc]
    _ = U * (-(entrywiseMatrixDerivation D A * U)) := by rw [hright]
    _ = -(U * entrywiseMatrixDerivation D A * U) := by
      rw [mul_neg, Matrix.mul_assoc]
end QEC.Coding.AlgebraicGeometry
