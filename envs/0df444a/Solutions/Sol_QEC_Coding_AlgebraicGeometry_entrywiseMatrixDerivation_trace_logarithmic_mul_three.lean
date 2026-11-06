-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_trace_logarithmic_mul_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:28:45.944391+00:00
-- url     : https://prove2.me/submissions/d5f2ab04-dc72-44eb-87ef-5e80e129ec90

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_MatrixDerivation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_mul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_add
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_one

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    {n : Type*} [Fintype n] [DecidableEq n]
    (D : Derivation k K K)
    (P Pinv A Ainv Q Qinv : Matrix n n K)
    (hPinvP : Pinv * P = 1)
    (hAinvA : Ainv * A = 1) (hAAinv : A * Ainv = 1)
    (hQQinv : Q * Qinv = 1) :
    Matrix.trace
        (Qinv * Ainv * Pinv *
          entrywiseMatrixDerivation D (P * A * Q)) =
      Matrix.trace (Pinv * entrywiseMatrixDerivation D P) +
        Matrix.trace (Ainv * entrywiseMatrixDerivation D A) +
          Matrix.trace (Qinv * entrywiseMatrixDerivation D Q) := by
  let DP := entrywiseMatrixDerivation D P
  let DA := entrywiseMatrixDerivation D A
  let DQ := entrywiseMatrixDerivation D Q
  have htermP :
      Matrix.trace (Qinv * Ainv * Pinv * (DP * A * Q)) =
        Matrix.trace (Pinv * DP) := by
    calc
      Matrix.trace (Qinv * Ainv * Pinv * (DP * A * Q)) =
          Matrix.trace ((Qinv * Ainv * Pinv * DP * A) * Q) := by
            congr 1
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Q * (Qinv * Ainv * Pinv * DP * A)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((Ainv * Pinv * DP) * A) := by
        congr 1
        calc
          Q * (Qinv * Ainv * Pinv * DP * A) =
              (Q * Qinv) * (Ainv * Pinv * DP * A) := by
                simp only [Matrix.mul_assoc]
          _ = Ainv * Pinv * DP * A := by rw [hQQinv, one_mul]
      _ = Matrix.trace (A * (Ainv * Pinv * DP)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Pinv * DP) := by
        congr 1
        calc
          A * (Ainv * Pinv * DP) =
              (A * Ainv) * (Pinv * DP) := by
                simp only [Matrix.mul_assoc]
          _ = Pinv * DP := by rw [hAAinv, one_mul]
  have htermA :
      Matrix.trace (Qinv * Ainv * Pinv * (P * DA * Q)) =
        Matrix.trace (Ainv * DA) := by
    calc
      Matrix.trace (Qinv * Ainv * Pinv * (P * DA * Q)) =
          Matrix.trace ((Qinv * Ainv * Pinv * P * DA) * Q) := by
            congr 1
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Q * (Qinv * Ainv * Pinv * P * DA)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Ainv * DA) := by
        congr 1
        calc
          Q * (Qinv * Ainv * Pinv * P * DA) =
              (Q * Qinv) * (Ainv * Pinv * P * DA) := by
                simp only [Matrix.mul_assoc]
          _ = Ainv * Pinv * P * DA := by rw [hQQinv, one_mul]
          _ = Ainv * (Pinv * P) * DA := by rw [Matrix.mul_assoc Ainv Pinv P]
          _ = Ainv * DA := by rw [hPinvP, mul_one]
  have htermQ :
      Matrix.trace (Qinv * Ainv * Pinv * (P * A * DQ)) =
        Matrix.trace (Qinv * DQ) := by
    congr 1
    calc
      Qinv * Ainv * Pinv * (P * A * DQ) =
          Qinv * Ainv * ((Pinv * P) * (A * DQ)) := by
            simp only [Matrix.mul_assoc]
      _ = Qinv * Ainv * (A * DQ) := by rw [hPinvP, one_mul]
      _ = Qinv * ((Ainv * A) * DQ) := by
        simp only [Matrix.mul_assoc]
      _ = Qinv * DQ := by rw [hAinvA, one_mul]
  calc
    Matrix.trace
        (Qinv * Ainv * Pinv *
          entrywiseMatrixDerivation D (P * A * Q)) =
        Matrix.trace (Qinv * Ainv * Pinv * (DP * A * Q)) +
          Matrix.trace (Qinv * Ainv * Pinv * (P * DA * Q)) +
            Matrix.trace (Qinv * Ainv * Pinv * (P * A * DQ)) := by
      dsimp only [DP, DA, DQ]
      rw [entrywiseMatrixDerivation_mul D (P * A) Q,
        entrywiseMatrixDerivation_mul D P A]
      simp only [mul_add, add_mul, Matrix.trace_add]
    _ = _ := by rw [htermP, htermA, htermQ]
end QEC.Coding.AlgebraicGeometry
