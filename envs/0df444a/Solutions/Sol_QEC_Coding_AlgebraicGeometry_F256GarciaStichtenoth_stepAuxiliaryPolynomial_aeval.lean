-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_aeval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:00:59.843187+00:00
-- url     : https://prove2.me/submissions/3b2be77a-51a1-41ee-92cb-daabe7bb5b2e

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Galois
import Mathlib.FieldTheory.PrimitiveElement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_AuxiliaryMinpoly
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryCoordinate_artinSchreier


set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K]
variable [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Polynomial.aeval (stepAuxiliaryCoordinate P x hx)
        (stepAuxiliaryPolynomial x) = 0 := by
  rw [stepAuxiliaryPolynomial, map_add, map_pow, aeval_X, map_sub, aeval_C]
  rw [Polynomial.aeval_X]
  change
    stepAuxiliaryCoordinate P x hx ^ 16 +
        (stepAuxiliaryCoordinate P x hx -
          stepFieldEmbedding P x hx (x ^ 17)) = 0
  rw [map_pow]
  linear_combination stepAuxiliaryCoordinate_artinSchreier P x hx
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
