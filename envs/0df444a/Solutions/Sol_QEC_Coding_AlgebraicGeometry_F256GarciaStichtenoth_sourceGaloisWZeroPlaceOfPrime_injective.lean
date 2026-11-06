-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroPlaceOfPrime_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:38:02.92721+00:00
-- url     : https://prove2.me/submissions/0a76d8c9-10a5-4118-83eb-8ee5700c0c33

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWFibres
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWGlobalPlaces

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wClosureAlgebra
attribute [local instance 3000] wClosureAlgebra
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wClosureSMul
attribute [local instance 3000] wClosureSMul
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wClosureModule
attribute [local instance 3000] wClosureModule
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wClosureFree
attribute [local instance 3000] wClosureFree
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wBaseFree
attribute [local instance 3000] wBaseFree
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wClosureFaithfulSMul
attribute [local instance 3000] wClosureFaithfulSMul
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wClosureScalarTower
attribute [local instance] wClosureScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wClosureTorsionFree
attribute [local instance] wClosureTorsionFree
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wClosureFiniteDimensional
attribute [local instance] wClosureFiniteDimensional
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wClosureIsGalois
attribute [local instance] wClosureIsGalois
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.oBaseModule
attribute [local instance 2000] oBaseModule
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.oBaseFaithfulSMul
attribute [local instance 2000] oBaseFaithfulSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.oClosureAlgebra
attribute [local instance 2000] oClosureAlgebra
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.oClosureSMul
attribute [local instance 2000] oClosureSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.oClosureModule
attribute [local instance 2000] oClosureModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.oBaseScalarTower
attribute [local instance] oBaseScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.oIntegralClosureFractionTower
attribute [local instance] oIntegralClosureFractionTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.oIntegralClosureTorsionFree
attribute [local instance] oIntegralClosureTorsionFree
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.oIntegralClosureFaithfulSMul
attribute [local instance] oIntegralClosureFaithfulSMul
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.oIntegralClosureFinite
attribute [local instance] oIntegralClosureFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.oIntegralClosureIsFractionRing
attribute [local instance] oIntegralClosureIsFractionRing
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.oIntegralClosureIsDedekind
attribute [local instance] oIntegralClosureIsDedekind
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ) :
    Function.Injective (sourceGaloisWZeroPlaceOfPrime m) := by
  intro P R hPR
  apply Subtype.ext
  ext x
  let HP := sourceGaloisWZeroUpperHeightOne m P
  let HR := sourceGaloisWZeroUpperHeightOne m R
  have hvaluation : HP.valuation (SourceGaloisClosureField m) =
      HR.valuation (SourceGaloisClosureField m) :=
    congrArg GlobalPlace.valuation hPR
  change x ∈ HP.asIdeal ↔ x ∈ HR.asIdeal
  rw [← HP.valuation_lt_one_iff_mem (K := SourceGaloisClosureField m), hvaluation,
    HR.valuation_lt_one_iff_mem]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
