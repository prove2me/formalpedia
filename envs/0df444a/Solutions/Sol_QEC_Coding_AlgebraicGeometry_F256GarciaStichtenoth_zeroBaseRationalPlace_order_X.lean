-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.zeroBaseRationalPlace_order_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:01:55.380871+00:00
-- url     : https://prove2.me/submissions/b34b358e-ff03-471f-b072-b8d7fed3b169

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasePlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialLogarithmicResidue
import Mathlib.RingTheory.Polynomial.Quotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ZeroPlace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdic_order_algebraMap_polynomial


set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution :
    zeroBaseRationalPlace.place.order RatFunc.X = 1 := by
  change (GlobalPlace.rationalAdic zeroBaseHeightOne).order RatFunc.X = 1
  rw [← RatFunc.algebraMap_X,
    GlobalPlace.rationalAdic_order_algebraMap_polynomial
      zeroBaseHeightOne Polynomial.X Polynomial.X_ne_zero,
    zeroBaseHeightOne_asIdeal, multiplicity_self]
  norm_num
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
