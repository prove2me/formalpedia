-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:20:57.806372+00:00
-- url     : https://prove2.me/submissions/8b069fd1-eb05-4a75-a692-5047bb9c6f70

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_MatrixDerivation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution {m n : Type*}
    (D : Derivation k K K) (A : Matrix m n K) (i : m) (j : n) :
    entrywiseMatrixDerivation D A i j = D (A i j) :=
  rfl
end QEC.Coding.AlgebraicGeometry
