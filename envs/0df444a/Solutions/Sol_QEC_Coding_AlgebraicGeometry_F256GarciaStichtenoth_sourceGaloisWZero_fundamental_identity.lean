-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZero_fundamental_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:59:10.807296+00:00
-- url     : https://prove2.me/submissions/5cd1c624-0ba8-46a3-b094-d4461bcef45c

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSelectedPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWClosurePlaces
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Valuation.AlgebraInstances
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWFibres
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing

section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2000] sourceGaloisWPlaceValuationRingBaseModule
attribute [local instance 2000] sourceGaloisWPlaceValuationRingBaseFaithfulSMul
attribute [local instance 3000] sourceGaloisWClosureFieldClosureAlgebra
attribute [local instance 3000] sourceGaloisWClosureFieldClosureSMul
attribute [local instance 3000] sourceGaloisWClosureFieldClosureModule
attribute [local instance 3000] sourceGaloisWClosureFieldClosureFree
attribute [local instance 3000] sourceGaloisWClosureFieldBaseFree
attribute [local instance 3000] sourceGaloisWClosureFieldClosureFaithfulSMul
attribute [local instance] sourceGaloisWClosureFieldClosureScalarTower
attribute [local instance] sourceGaloisWClosureFieldClosureTorsionFree
attribute [local instance] sourceGaloisWClosureFieldClosureFiniteDimensional
attribute [local instance] sourceGaloisWClosureFieldClosureIsGalois
attribute [local instance 2000] sourceGaloisWPlaceValuationRingClosureAlgebra
attribute [local instance 2000] sourceGaloisWPlaceValuationRingClosureSMul
attribute [local instance 2000] sourceGaloisWPlaceValuationRingClosureModule
attribute [local instance] sourceGaloisWPlaceBaseScalarTower
attribute [local instance] sourceGaloisWPlaceIntegralClosureFractionTower
attribute [local instance] sourceGaloisWRelativeGalFinite
attribute [local instance] sourceGaloisWPlaceIntegralClosureTorsionFree
attribute [local instance] sourceGaloisWPlaceIntegralClosureFaithfulSMul
attribute [local instance] sourceGaloisWPlaceIntegralClosureFinite
attribute [local instance] sourceGaloisWPlaceIntegralClosureIsFractionRing
attribute [local instance] sourceGaloisWPlaceIntegralClosureIsDedekind
attribute [local instance] sourceGaloisWPlaceIntegralClosureAction
attribute [local instance] sourceGaloisWPlaceIntegralClosureIsGaloisGroup
private theorem sourceGaloisWPlace_fundamental_identity (m : ℕ)
    (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    Set.ncard
        ((IsLocalRing.maximalIdeal P.valuationRing).primesOver
          (SourceGaloisWPlaceIntegralClosure m P)) *
        ((IsLocalRing.maximalIdeal P.valuationRing).ramificationIdxIn
            (SourceGaloisWPlaceIntegralClosure m P) *
          (IsLocalRing.maximalIdeal P.valuationRing).inertiaDegIn
            (SourceGaloisWPlaceIntegralClosure m P)) =
      Module.finrank (SourceGaloisWClosureField m) (SourceGaloisClosureField m) := by
  let O := P.valuationRing
  let C := SourceGaloisWPlaceIntegralClosure m P
  let p : Ideal O := IsLocalRing.maximalIdeal O
  let G := Gal((SourceGaloisClosureField m) / (SourceGaloisWClosureField m))
  letI : IsDiscreteValuationRing O :=
    P.valuationRing_isDiscreteValuationRing
  calc
    Set.ncard (p.primesOver C) *
        (p.ramificationIdxIn C * p.inertiaDegIn C) = Nat.card G :=
      Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p C G
    _ = Module.finrank (SourceGaloisWClosureField m) (SourceGaloisClosureField m) :=
      IsGalois.card_aut_eq_finrank (SourceGaloisWClosureField m)
        (SourceGaloisClosureField m)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPlaceValuationRingBaseModule
attribute [local instance 2000] sourceGaloisWPlaceValuationRingBaseModule
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPlaceValuationRingBaseFaithfulSMul
attribute [local instance 2000] sourceGaloisWPlaceValuationRingBaseFaithfulSMul
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureFieldClosureAlgebra
attribute [local instance 3000] sourceGaloisWClosureFieldClosureAlgebra
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureFieldClosureSMul
attribute [local instance 3000] sourceGaloisWClosureFieldClosureSMul
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureFieldClosureModule
attribute [local instance 3000] sourceGaloisWClosureFieldClosureModule
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureFieldClosureFree
attribute [local instance 3000] sourceGaloisWClosureFieldClosureFree
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureFieldBaseFree
attribute [local instance 3000] sourceGaloisWClosureFieldBaseFree
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureFieldClosureFaithfulSMul
attribute [local instance 3000] sourceGaloisWClosureFieldClosureFaithfulSMul
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureFieldClosureScalarTower
attribute [local instance] sourceGaloisWClosureFieldClosureScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureFieldClosureTorsionFree
attribute [local instance] sourceGaloisWClosureFieldClosureTorsionFree
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureFieldClosureFiniteDimensional
attribute [local instance] sourceGaloisWClosureFieldClosureFiniteDimensional
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureFieldClosureIsGalois
attribute [local instance] sourceGaloisWClosureFieldClosureIsGalois
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPlaceValuationRingClosureAlgebra
attribute [local instance 2000] sourceGaloisWPlaceValuationRingClosureAlgebra
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPlaceValuationRingClosureSMul
attribute [local instance 2000] sourceGaloisWPlaceValuationRingClosureSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPlaceValuationRingClosureModule
attribute [local instance 2000] sourceGaloisWPlaceValuationRingClosureModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPlaceBaseScalarTower
attribute [local instance] sourceGaloisWPlaceBaseScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPlaceIntegralClosureFractionTower
attribute [local instance] sourceGaloisWPlaceIntegralClosureFractionTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWRelativeGalFinite
attribute [local instance] sourceGaloisWRelativeGalFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPlaceIntegralClosureTorsionFree
attribute [local instance] sourceGaloisWPlaceIntegralClosureTorsionFree
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPlaceIntegralClosureFaithfulSMul
attribute [local instance] sourceGaloisWPlaceIntegralClosureFaithfulSMul
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPlaceIntegralClosureFinite
attribute [local instance] sourceGaloisWPlaceIntegralClosureFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPlaceIntegralClosureIsFractionRing
attribute [local instance] sourceGaloisWPlaceIntegralClosureIsFractionRing
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPlaceIntegralClosureIsDedekind
attribute [local instance] sourceGaloisWPlaceIntegralClosureIsDedekind
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPlaceIntegralClosureAction
attribute [local instance] sourceGaloisWPlaceIntegralClosureAction
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPlaceIntegralClosureIsGaloisGroup
attribute [local instance] sourceGaloisWPlaceIntegralClosureIsGaloisGroup
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ) :
    Set.ncard (SourceGaloisWZeroPrime m) *
        (sourceGaloisWZeroRamificationIndex m *
          sourceGaloisWZeroInertiaDegree m) =
      Module.finrank (SourceGaloisWClosureField m) (SourceGaloisClosureField m) := by
  exact sourceGaloisWPlace_fundamental_identity m (sourceGaloisWClosureZeroPlace m)
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
