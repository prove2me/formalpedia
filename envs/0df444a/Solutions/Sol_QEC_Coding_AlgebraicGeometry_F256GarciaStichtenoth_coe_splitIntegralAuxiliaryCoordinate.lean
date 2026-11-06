-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_splitIntegralAuxiliaryCoordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:49:31.898342+00:00
-- url     : https://prove2.me/submissions/5915250e-e395-4dda-a4d5-bcda9bf8ccb0

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ResidualPolynomial
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplitIntegralClosure

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    (splitIntegralAuxiliaryCoordinate Q P x hx hregular :
        StepField P x hx) =
      stepAuxiliaryCoordinate P x hx :=
  rfl
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
