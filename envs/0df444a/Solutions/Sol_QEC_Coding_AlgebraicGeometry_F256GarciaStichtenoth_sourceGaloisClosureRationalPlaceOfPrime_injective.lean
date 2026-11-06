-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureRationalPlaceOfPrime_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:53:41.85879+00:00
-- url     : https://prove2.me/submissions/ea36ff8a-50b3-4357-8582-fe8e1d8db6ff

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisFunctionField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosureSplitting
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSelectedPlaces
section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2000] galoisSelectedBaseValuationRingBaseModule
attribute [local instance 2000] galoisSelectedBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] galoisSelectedBaseValuationRingAlgebra
attribute [local instance 2000] galoisSelectedBaseValuationRingSMul
attribute [local instance 2000] galoisSelectedBaseValuationRingModule
attribute [local instance] galoisSelectedBaseScalarTower
attribute [local instance] galoisSelectedIntegralClosureFractionTower
attribute [local instance] galoisSelectedIntegralClosureTorsionFree
attribute [local instance] galoisSelectedIntegralClosureFinite
attribute [local instance] galoisSelectedIntegralClosureIsFractionRing
attribute [local instance] galoisSelectedIntegralClosureIsDedekind
private theorem sourceGaloisClosurePlaceOfPrime_injective (m : ℕ) :
    Function.Injective (sourceGaloisClosurePlaceOfPrime m) := by
  intro P Q hPQ
  apply Subtype.ext
  ext x
  let HP := sourceGaloisClosureUpperHeightOne m P
  let HQ := sourceGaloisClosureUpperHeightOne m Q
  have hvaluation : HP.valuation (SourceGaloisClosureField m) =
      HQ.valuation (SourceGaloisClosureField m) :=
    congrArg GlobalPlace.valuation hPQ
  change x ∈ HP.asIdeal ↔ x ∈ HQ.asIdeal
  rw [← HP.valuation_lt_one_iff_mem (K := SourceGaloisClosureField m),
    hvaluation, HQ.valuation_lt_one_iff_mem]
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

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
    Function.Injective (sourceGaloisClosureRationalPlaceOfPrime m) := by
  intro P Q hPQ
  apply sourceGaloisClosurePlaceOfPrime_injective m
  exact congrArg RationalPlace.place hPQ
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
