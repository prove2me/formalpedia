-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:32:54.692396+00:00
-- url     : https://prove2.me/submissions/5e726831-8e71-47d6-9585-5b9122cd789e

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Galois
import Mathlib.FieldTheory.PrimitiveElement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_AuxiliaryMinpoly
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_minpoly_stepAuxiliaryCoordinate

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K]
variable [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Irreducible (stepAuxiliaryPolynomial x) := by
  rw [← minpoly_stepAuxiliaryCoordinate P x hx]
  exact minpoly.irreducible (IsIntegral.of_finite K _)
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
