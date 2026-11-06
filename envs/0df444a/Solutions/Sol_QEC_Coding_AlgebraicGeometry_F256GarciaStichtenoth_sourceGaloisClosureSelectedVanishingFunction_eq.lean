-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureSelectedVanishingFunction_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:24:08.354795+00:00
-- url     : https://prove2.me/submissions/66dcffa8-6fcf-4c50-a74c-3c5beef2dd0d

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSelectedPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPrincipalDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_FinitePlaceDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSelectedDivisor

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
open IntermediateField
open scoped BigOperators Polynomial RatFunc
noncomputable section
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_closurePolynomialAlgebra
attribute [local instance] sourceGaloisSelectedDivisor_closurePolynomialAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_closurePolynomialRatFuncScalarTower
attribute [local instance] sourceGaloisSelectedDivisor_closurePolynomialRatFuncScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_closureRatFuncIsSeparable
attribute [local instance] sourceGaloisSelectedDivisor_closureRatFuncIsSeparable
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ) :
    sourceGaloisClosureSelectedVanishingFunction m =
      ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : sourceGaloisSelectedDivisor_E m) ^ 15 - 1 :=
  rfl
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
