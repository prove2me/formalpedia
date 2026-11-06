-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ArtinSchreier.artinSchreierPolynomial_separable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:42:48.251809+00:00
-- url     : https://prove2.me/submissions/afa6c27f-d1e7-481e-a441-7df737a11f03

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ArtinSchreier

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ArtinSchreier
open scoped WithZero BigOperators
open Polynomial
variable {F : Type*} [Field F]
namespace QEC.Coding.AlgebraicGeometry.ArtinSchreier
theorem _root_.solution [CharP F 2] (u : F) :
    (artinSchreierPolynomial u).Separable := by
  rw [artinSchreierPolynomial]
  have hrewrite : (X ^ 32 + X - C u : F[X]) =
      C 1 * X ^ 32 + C 1 * X + C (-u) := by
    simp only [map_one, one_mul, C_neg]
    ring
  rw [hrewrite]
  exact separable_C_mul_X_pow_add_C_mul_X_add_C' 2 32 (1 : F) 1 (-u)
    (by norm_num) isUnit_one
end QEC.Coding.AlgebraicGeometry.ArtinSchreier
