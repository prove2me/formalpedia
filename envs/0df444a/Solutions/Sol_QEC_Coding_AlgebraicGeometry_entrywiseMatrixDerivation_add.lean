-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:21:52.619895+00:00
-- url     : https://prove2.me/submissions/53a92e4b-b597-4140-8fb0-3daceaa5a79e

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_MatrixDerivation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution {m n : Type*}
    (D : Derivation k K K) (A B : Matrix m n K) :
    entrywiseMatrixDerivation D (A + B) =
      entrywiseMatrixDerivation D A + entrywiseMatrixDerivation D B := by
  ext i j
  simp only [entrywiseMatrixDerivation_apply, Matrix.add_apply, map_add]
end QEC.Coding.AlgebraicGeometry
