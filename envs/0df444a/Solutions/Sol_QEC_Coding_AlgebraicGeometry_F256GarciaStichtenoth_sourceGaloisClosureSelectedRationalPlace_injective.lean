-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureSelectedRationalPlace_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:36:25.086857+00:00
-- url     : https://prove2.me/submissions/eddc4ffa-3cfb-48b9-bc07-cfc754e8c97f

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisFunctionField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosureSplitting
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSelectedPlaces
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisClosureRationalPlaceOfPrime_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.galoisSelectedBaseValuationRingBaseModule
attribute [local instance 2000] galoisSelectedBaseValuationRingBaseModule
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.galoisSelectedBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] galoisSelectedBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.galoisSelectedBaseValuationRingAlgebra
attribute [local instance 2000] galoisSelectedBaseValuationRingAlgebra
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.galoisSelectedBaseValuationRingSMul
attribute [local instance 2000] galoisSelectedBaseValuationRingSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.galoisSelectedBaseValuationRingModule
attribute [local instance 2000] galoisSelectedBaseValuationRingModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.galoisSelectedBaseScalarTower
attribute [local instance] galoisSelectedBaseScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.galoisSelectedIntegralClosureFractionTower
attribute [local instance] galoisSelectedIntegralClosureFractionTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.galoisSelectedIntegralClosureTorsionFree
attribute [local instance] galoisSelectedIntegralClosureTorsionFree
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.galoisSelectedIntegralClosureFinite
attribute [local instance] galoisSelectedIntegralClosureFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.galoisSelectedIntegralClosureIsFractionRing
attribute [local instance] galoisSelectedIntegralClosureIsFractionRing
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.galoisSelectedIntegralClosureIsDedekind
attribute [local instance] galoisSelectedIntegralClosureIsDedekind
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ) :
    Function.Injective (sourceGaloisClosureSelectedRationalPlace m) := by
  intro i j hij
  apply (sourceGaloisClosureSelectedPrimeEquiv m).injective
  apply sourceGaloisClosureRationalPlaceOfPrime_injective m
  exact hij
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
