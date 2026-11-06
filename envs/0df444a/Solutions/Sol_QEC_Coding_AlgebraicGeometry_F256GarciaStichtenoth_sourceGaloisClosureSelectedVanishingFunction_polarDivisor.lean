-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureSelectedVanishingFunction_polarDivisor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:27:58.143991+00:00
-- url     : https://prove2.me/submissions/d547ee45-a29b-4cec-9c32-5aded482277c

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSelectedPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPrincipalDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_FinitePlaceDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSelectedDivisor
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisClosureSelectedVanishingFunction_eq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceGaloisWFieldGenerator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceSplitIntegralCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_splitIntegralAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWClosureGeneratorPoleDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWClosureGenerator_polarDivisor
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWFieldEquivRatFunc_X
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityFibreDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWZeroFibreDivisor_apply
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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_finitePlaceDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_mem_valuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_order_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_reciprocalUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceGaloisWFieldGenerator
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceSplitIntegralCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_splitIntegralAuxiliaryCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureGeneratorPoleDivisor_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWFieldEquivRatFunc_X
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWInfinityFibreDivisor_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroFibreDivisor_apply
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
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.finitePlaceDivisor_apply
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
open IntermediateField
open scoped BigOperators Polynomial RatFunc
noncomputable section
attribute [local instance] sourceGaloisSelectedDivisor_closurePolynomialAlgebra
attribute [local instance] sourceGaloisSelectedDivisor_closurePolynomialRatFuncScalarTower
attribute [local instance] sourceGaloisSelectedDivisor_closureRatFuncIsSeparable
private theorem sourceGaloisSelectedDivisor_selectedVanishingFunction_order_of_generator_order_neg
    (m : ℕ) (P : GlobalPlace F256 (sourceGaloisSelectedDivisor_E m))
    (horder : P.order
      ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : sourceGaloisSelectedDivisor_E m) < 0) :
    P.order (sourceGaloisClosureSelectedVanishingFunction m) =
      15 * P.order
        ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : sourceGaloisSelectedDivisor_E m) := by
  let w : sourceGaloisSelectedDivisor_E m :=
    (sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m)
  have hw : w ≠ 0 := sourceGaloisWClosureGenerator_ne_zero m
  have hwpow : w ^ 15 ≠ 0 := pow_ne_zero 15 hw
  have horderPow : P.order (w ^ 15) < 0 := by
    rw [sourceGaloisSelectedDivisor_order_pow]
    exact mul_neg_of_pos_of_neg (by norm_num) horder
  have hvaluationPow : 1 < P.valuation (w ^ 15) := by
    change WithZero.exp (0 : ℤ) < P.valuation (w ^ 15)
    rw [← WithZero.lt_log_iff_exp_lt
      ((P.valuation).ne_zero_iff.mpr hwpow)]
    unfold GlobalPlace.order at horderPow
    omega
  have hvaluationSub : P.valuation (w ^ 15 - 1) =
      P.valuation (w ^ 15) :=
    (P.valuation).map_sub_eq_of_lt_left (by
      simpa only [map_one] using hvaluationPow)
  rw [sourceGaloisClosureSelectedVanishingFunction_eq]
  change P.order (w ^ 15 - 1) = 15 * P.order w
  calc
    P.order (w ^ 15 - 1) = P.order (w ^ 15) := by
      unfold GlobalPlace.order
      rw [hvaluationSub]
    _ = 15 * P.order w := sourceGaloisSelectedDivisor_order_pow m 15 P w
private theorem sourceGaloisSelectedDivisor_selectedVanishingFunction_order_nonnegative_of_generator_order_nonnegative
    (m : ℕ) (P : GlobalPlace F256 (sourceGaloisSelectedDivisor_E m))
    (horder : 0 ≤ P.order
      ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : sourceGaloisSelectedDivisor_E m)) :
    0 ≤ P.order (sourceGaloisClosureSelectedVanishingFunction m) := by
  let w : sourceGaloisSelectedDivisor_E m :=
    (sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m)
  have hw : w ≠ 0 := sourceGaloisWClosureGenerator_ne_zero m
  have hwRegular : GlobalPlace.RegularAt P w :=
    (P.regularAt_iff_order_nonnegative hw).mpr horder
  have hwMem : w ∈ P.valuationRing :=
    (P.regularAt_iff_mem_valuationRing w).mp hwRegular
  have hsubMem : w ^ 15 - 1 ∈ P.valuationRing :=
    P.valuationRing.sub_mem (P.valuationRing.pow_mem hwMem 15)
      P.valuationRing.one_mem
  apply (P.regularAt_iff_order_nonnegative
    (sourceGaloisClosureSelectedVanishingFunction_ne_zero m)).mp
  rw [sourceGaloisClosureSelectedVanishingFunction_eq]
  exact (P.regularAt_iff_mem_valuationRing (w ^ 15 - 1)).mpr hsubMem
private theorem sourceGaloisSelectedDivisor_selectedVanishingFunctionPoleDivisor_eq_smul_generatorPole
    (m : ℕ) :
    sourceGaloisClosureSelectedVanishingFunctionPoleDivisor m =
      15 • sourceGaloisWClosureGeneratorPoleDivisor m := by
  have hf' : sourceGaloisClosureSelectedVanishingFunction m ≠ 0 :=
    sourceGaloisClosureSelectedVanishingFunction_ne_zero m
  ext P
  unfold sourceGaloisClosureSelectedVanishingFunctionPoleDivisor
  rw [dif_neg hf']
  simp only [Finsupp.sup_apply, Finsupp.neg_apply, Finsupp.zero_apply,
    GlobalPlace.principalDivisor_apply, Units.val_mk0,
    Finsupp.smul_apply, nsmul_eq_mul,
    sourceGaloisWClosureGeneratorPoleDivisor_apply]
  by_cases horder : 0 ≤ P.order
      ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : sourceGaloisSelectedDivisor_E m)
  · have hforder : 0 ≤ P.order
        (sourceGaloisClosureSelectedVanishingFunction m) :=
      sourceGaloisSelectedDivisor_selectedVanishingFunction_order_nonnegative_of_generator_order_nonnegative
        m P horder
    rw [max_eq_right (by omega), max_eq_right (by omega)]
    simp
  · have horderNeg : P.order
        ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : sourceGaloisSelectedDivisor_E m) < 0 :=
      lt_of_not_ge horder
    have hforder := sourceGaloisSelectedDivisor_selectedVanishingFunction_order_of_generator_order_neg
      m P horderNeg
    rw [hforder, max_eq_left (by omega), max_eq_left (by omega)]
    ring
attribute [local instance 2000] sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingBaseModule
attribute [local instance 2000] sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingAlgebra
attribute [local instance 2000] sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingSMul
attribute [local instance 2000] sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingModule
attribute [local instance] sourceGaloisSelectedDivisor_selectedDivisorBaseScalarTower
attribute [local instance] sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureFractionTower
attribute [local instance] sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureTorsionFree
attribute [local instance] sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureFinite
attribute [local instance] sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureIsFractionRing
attribute [local instance] sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureIsDedekind
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

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
    sourceGaloisClosureSelectedVanishingFunctionPoleDivisor m =
      (15 * sourceGaloisWInfinityRamificationIndex m) •
        sourceGaloisWInfinityFibreDivisor m := by
  rw [sourceGaloisSelectedDivisor_selectedVanishingFunctionPoleDivisor_eq_smul_generatorPole,
    sourceGaloisWClosureGenerator_polarDivisor]
  simp only [smul_smul]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
