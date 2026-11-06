-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosure_exists_of_regularAt_selected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:34:32.400091+00:00
-- url     : https://prove2.me/submissions/0e0422c9-bfa2-47ad-89f8-f8fe6f49e4d5

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedBaseRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_StepPlaceTransport
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Valuation.LocalSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSeedSplittingIdeals
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseValuationRingBaseModule
attribute [local instance 2000] sourceSeedBaseValuationRingBaseModule
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] sourceSeedBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseValuationRingAlgebra
attribute [local instance 2000] sourceSeedBaseValuationRingAlgebra
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseValuationRingSMul
attribute [local instance 2000] sourceSeedBaseValuationRingSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseValuationRingModule
attribute [local instance 2000] sourceSeedBaseValuationRingModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseScalarTower
attribute [local instance] sourceSeedBaseScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureTorsionFree
attribute [local instance] sourceSeedIntegralClosureTorsionFree
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureFinite
attribute [local instance] sourceSeedIntegralClosureFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureIsFractionRing
attribute [local instance] sourceSeedIntegralClosureIsFractionRing
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureIsDedekind
attribute [local instance] sourceSeedIntegralClosureIsDedekind
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ)
    (x : SourceField m)
    (hx : ∀ index : SourceSelectedPlaceIndex m,
      GlobalPlace.RegularAt (sourceSelectedRationalPlace m index).place x) :
    ∃ xO : SourceSeedIntegralClosure m,
      algebraMap (SourceSeedIntegralClosure m) (SourceField m) xO = x := by
  let O := SourceSeedBaseValuationRing
  let C := SourceSeedIntegralClosure m
  let L := SourceField m
  letI : IsDiscreteValuationRing O :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one L x
  intro H
  have hcomap_ne : H.asIdeal.comap (algebraMap O C) ≠ ⊥ :=
    Ideal.IsIntegral.comap_ne_bot O H.ne_bot
  have hcomap_max :
      (H.asIdeal.comap (algebraMap O C)).IsMaximal :=
    (H.isPrime.comap (algebraMap O C)).isMaximal hcomap_ne
  have hover : H.asIdeal.LiesOver (IsLocalRing.maximalIdeal O) := by
    constructor
    exact (IsLocalRing.eq_maximalIdeal hcomap_max).symm
  let P : (IsLocalRing.maximalIdeal O).primesOver C := by
    letI : H.asIdeal.LiesOver (IsLocalRing.maximalIdeal O) := hover
    exact Ideal.primesOver.mk (IsLocalRing.maximalIdeal O) H.asIdeal
  let index : SourceSelectedPlaceIndex m :=
    (sourceSeedUpperPrimeEquiv m).symm P
  have hprime : sourceSeedUpperPrime m index = P :=
    (sourceSeedUpperPrimeEquiv m).apply_symm_apply P
  have hheight : sourceSeedUpperHeightOne m index = H := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    change (sourceSeedUpperPrime m index).1 = P.1
    exact congrArg Subtype.val hprime
  have hxSelected : x ∈
      (sourceSelectedRationalPlace m index).place.valuationRing :=
    (GlobalPlace.mem_valuationRing_iff
      (sourceSelectedRationalPlace m index).place x).mpr (hx index)
  have hxCanonical : x ∈ sourceSeedUpperCanonicalLocalization m index := by
    rw [sourceSeedUpperCanonicalLocalization_eq_valuationRing]
    exact hxSelected
  have hxAtH : x ∈ H.valuationSubringAtPrime L := by
    rw [← hheight]
    exact hxCanonical
  have hxValuationSubring : x ∈ (H.valuation L).valuationSubring := by
    rw [← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    exact hxAtH
  exact ((H.valuation L).mem_valuationSubring_iff x).mp hxValuationSubring
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
