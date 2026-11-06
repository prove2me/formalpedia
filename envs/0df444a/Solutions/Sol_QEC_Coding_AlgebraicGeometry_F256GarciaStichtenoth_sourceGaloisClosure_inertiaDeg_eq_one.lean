-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosure_inertiaDeg_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:44:41.847359+00:00
-- url     : https://prove2.me/submissions/bc3ab659-6e50-4a48-95ad-d4b69e9d710b

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSeedSplittingIdeals
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosure
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Coset.Card
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Valuation.AlgebraInstances
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosureSplitting
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisClosure_primesOver_ncard_eq_finrank
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceSplitIntegralCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_splitIntegralAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisClosureField_finrank_lower_bound
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSplitUpperRationalPlace_place
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepResidualPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_splitUpperRationalPlace_place
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepDistinguishedCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepFieldEmbedding
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepReciprocalRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_comapAlgEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_reciprocalUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceSplitIntegralCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_splitIntegralAuxiliaryCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitUpperRationalPlace_place
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepResidualPolynomial_natDegree
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.splitUpperRationalPlace_place
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_natDegree
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepAuxiliaryCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepDistinguishedCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepFieldEmbedding
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepReciprocalRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.comapAlgEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
open scoped Pointwise
attribute [local instance 3000] sourceGaloisClosureFieldBaseAlgebraPinned
attribute [local instance 3000] sourceGaloisClosureFieldBaseSMulPinned
attribute [local instance 3000] sourceGaloisClosureFieldBaseModulePinned
attribute [local instance 3000] sourceGaloisClosureGalFinite
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingBaseModule
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] sourceGaloisClosureSeedBaseValuationRingAlgebra
attribute [local instance 2000] sourceGaloisClosureSeedBaseValuationRingSMul
attribute [local instance 2000] sourceGaloisClosureSeedBaseValuationRingModule
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingAlgebra
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingSMul
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingModule
attribute [local instance] sourceGaloisClosureBaseScalarTower
attribute [local instance] sourceGaloisClosureSeedBaseScalarTower
attribute [local instance] sourceSeedIntegralClosureFractionTower
attribute [local instance] sourceGaloisClosureIntegralClosureFractionTower
attribute [local instance] sourceSeedIntegralClosureClosureAlgebra
attribute [local instance 2000] sourceSeedIntegralClosureClosureSMul
attribute [local instance 2000] sourceSeedIntegralClosureClosureModule
attribute [local instance] sourceGaloisClosureIntegralClosureScalarTower
attribute [local instance] sourceGaloisClosureIntegralOverSeedIntegral
attribute [local instance] sourceGaloisClosureIntegralOverSeedTorsionFree
attribute [local instance] sourceGaloisClosureIntegralClosureTorsionFree
attribute [local instance] sourceGaloisClosureIntegralClosureFinite
attribute [local instance] sourceGaloisClosureIntegralClosureIsFractionRing
attribute [local instance] sourceGaloisClosureIntegralClosureIsDedekind
attribute [local instance] sourceGaloisClosureIntegralClosureAction
attribute [local instance 3000] sourceGaloisClosureIntegralClosureSMul
attribute [local instance 3000] sourceGaloisClosureIntegralClosureIdealAction
attribute [local instance 4000] sourceGaloisClosureIntegralClosureIdealMulAction
attribute [local instance] sourceGaloisClosureIntegralClosureActionCommutesWithBase
attribute [local instance] sourceGaloisClosureIntegralClosureIsGaloisGroup
attribute [local instance 3000] sourceSeedClosureFieldRangeAlgebra
attribute [local instance 3000] sourceSeedClosureFieldRangeSMul
attribute [local instance 3000] sourceSeedClosureFieldRangeModule
private theorem sourceGaloisClosure_ramificationIdxIn_mul_inertiaDegIn_eq_one
    (m : ℕ) :
    (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).ramificationIdxIn
          (SourceGaloisClosureIntegralClosure m) *
        (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).inertiaDegIn
          (SourceGaloisClosureIntegralClosure m) = 1 := by
  let O := SourceSeedBaseValuationRing
  let C := SourceGaloisClosureIntegralClosure m
  let p : Ideal O := IsLocalRing.maximalIdeal O
  let G := Gal((SourceGaloisClosureField m) / GaloisBaseField)
  letI : IsDiscreteValuationRing O :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  letI : Module.IsTorsionFree O C := by
    change Module.IsTorsionFree SourceSeedBaseValuationRing
      (SourceGaloisClosureIntegralClosure m)
    exact sourceGaloisClosureIntegralClosureTorsionFree m
  letI : Module.Finite O C := by
    change Module.Finite SourceSeedBaseValuationRing
      (SourceGaloisClosureIntegralClosure m)
    exact sourceGaloisClosureIntegralClosureFinite m
  have hfundamental :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      p C G
  rw [sourceGaloisClosure_primesOver_ncard_eq_finrank m,
    IsGalois.card_aut_eq_finrank GaloisBaseField (SourceGaloisClosureField m)]
      at hfundamental
  have hcancel :
      Module.finrank GaloisBaseField (SourceGaloisClosureField m) *
          (p.ramificationIdxIn C * p.inertiaDegIn C) =
        Module.finrank GaloisBaseField (SourceGaloisClosureField m) * 1 := by
    simpa only [Nat.mul_one] using hfundamental
  have hproductIn : p.ramificationIdxIn C * p.inertiaDegIn C = 1 :=
    Nat.mul_left_cancel
      (lt_of_lt_of_le (by positivity) (sourceGaloisClosureField_finrank_lower_bound m))
      hcancel
  exact hproductIn
private theorem sourceGaloisClosure_ramificationIdx_mul_inertiaDeg_eq_one
    (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).ramificationIdx' P.1 *
      (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).inertiaDeg' P.1 = 1 := by
  let O := SourceSeedBaseValuationRing
  let C := SourceGaloisClosureIntegralClosure m
  let p : Ideal O := IsLocalRing.maximalIdeal O
  let G := Gal((SourceGaloisClosureField m) / GaloisBaseField)
  letI : IsDiscreteValuationRing O :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  have hp0 : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  letI : p.IsMaximal := inferInstance
  letI : P.1.IsPrime := P.2.1
  letI : P.1.LiesOver p := P.2.2
  have hP0 : P.1 ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hp0 P.2
  letI : P.1.IsMaximal := P.2.1.isMaximal hP0
  have hproductIn : p.ramificationIdxIn C * p.inertiaDegIn C = 1 :=
    sourceGaloisClosure_ramificationIdxIn_mul_inertiaDegIn_eq_one m
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P.1 G,
    Ideal.inertiaDegIn_eq_inertiaDeg p P.1 G] at hproductIn
  change p.ramificationIdx' P.1 * p.inertiaDeg' P.1 = 1
  rw [Ideal.ramificationIdx'_eq_ramificationIdx p P.1 hp0,
    Ideal.inertiaDeg'_eq_inertiaDeg]
  exact hproductIn
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
open scoped Pointwise
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureFieldBaseAlgebraPinned
attribute [local instance 3000] sourceGaloisClosureFieldBaseAlgebraPinned
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureFieldBaseSMulPinned
attribute [local instance 3000] sourceGaloisClosureFieldBaseSMulPinned
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureFieldBaseModulePinned
attribute [local instance 3000] sourceGaloisClosureFieldBaseModulePinned
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureGalFinite
attribute [local instance 3000] sourceGaloisClosureGalFinite
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureBaseValuationRingBaseModule
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingBaseModule
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureSeedBaseValuationRingAlgebra
attribute [local instance 2000] sourceGaloisClosureSeedBaseValuationRingAlgebra
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureSeedBaseValuationRingSMul
attribute [local instance 2000] sourceGaloisClosureSeedBaseValuationRingSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureSeedBaseValuationRingModule
attribute [local instance 2000] sourceGaloisClosureSeedBaseValuationRingModule
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureBaseValuationRingAlgebra
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingAlgebra
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureBaseValuationRingSMul
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureBaseValuationRingModule
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureBaseScalarTower
attribute [local instance] sourceGaloisClosureBaseScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureSeedBaseScalarTower
attribute [local instance] sourceGaloisClosureSeedBaseScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureFractionTower
attribute [local instance] sourceSeedIntegralClosureFractionTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureFractionTower
attribute [local instance] sourceGaloisClosureIntegralClosureFractionTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureClosureAlgebra
attribute [local instance] sourceSeedIntegralClosureClosureAlgebra
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureClosureSMul
attribute [local instance 2000] sourceSeedIntegralClosureClosureSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureClosureModule
attribute [local instance 2000] sourceSeedIntegralClosureClosureModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureScalarTower
attribute [local instance] sourceGaloisClosureIntegralClosureScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralOverSeedIntegral
attribute [local instance] sourceGaloisClosureIntegralOverSeedIntegral
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralOverSeedTorsionFree
attribute [local instance] sourceGaloisClosureIntegralOverSeedTorsionFree
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureTorsionFree
attribute [local instance] sourceGaloisClosureIntegralClosureTorsionFree
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureFinite
attribute [local instance] sourceGaloisClosureIntegralClosureFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureIsFractionRing
attribute [local instance] sourceGaloisClosureIntegralClosureIsFractionRing
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureIsDedekind
attribute [local instance] sourceGaloisClosureIntegralClosureIsDedekind
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureAction
attribute [local instance] sourceGaloisClosureIntegralClosureAction
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureSMul
attribute [local instance 3000] sourceGaloisClosureIntegralClosureSMul
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureIdealAction
attribute [local instance 3000] sourceGaloisClosureIntegralClosureIdealAction
attribute [local instance 4000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureIdealMulAction
attribute [local instance 4000] sourceGaloisClosureIntegralClosureIdealMulAction
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureActionCommutesWithBase
attribute [local instance] sourceGaloisClosureIntegralClosureActionCommutesWithBase
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureIntegralClosureIsGaloisGroup
attribute [local instance] sourceGaloisClosureIntegralClosureIsGaloisGroup
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedClosureFieldRangeAlgebra
attribute [local instance 3000] sourceSeedClosureFieldRangeAlgebra
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedClosureFieldRangeSMul
attribute [local instance 3000] sourceSeedClosureFieldRangeSMul
attribute [local instance 3000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedClosureFieldRangeModule
attribute [local instance 3000] sourceSeedClosureFieldRangeModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).inertiaDeg'
      P.1 = 1 := by
  apply Nat.eq_one_of_dvd_one
  refine ⟨(IsLocalRing.maximalIdeal
      SourceSeedBaseValuationRing).ramificationIdx' P.1, ?_⟩
  calc
    1 = (IsLocalRing.maximalIdeal
          SourceSeedBaseValuationRing).ramificationIdx' P.1 *
        (IsLocalRing.maximalIdeal
          SourceSeedBaseValuationRing).inertiaDeg' P.1 :=
      (sourceGaloisClosure_ramificationIdx_mul_inertiaDeg_eq_one m P).symm
    _ = (IsLocalRing.maximalIdeal
          SourceSeedBaseValuationRing).inertiaDeg' P.1 *
        (IsLocalRing.maximalIdeal
          SourceSeedBaseValuationRing).ramificationIdx' P.1 := Nat.mul_comm _ _
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
