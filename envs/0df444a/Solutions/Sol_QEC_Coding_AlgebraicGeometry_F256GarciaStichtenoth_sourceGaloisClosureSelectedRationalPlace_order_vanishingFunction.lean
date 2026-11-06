-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureSelectedRationalPlace_order_vanishingFunction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:31:23.551833+00:00
-- url     : https://prove2.me/submissions/48d1faaf-c77a-46b3-ad75-a16eebd936bd

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSelectedPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPrincipalDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_FinitePlaceDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSelectedDivisor
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisClosureSelectedDivisor_degree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisClosureSelectedVanishingFunction_eq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisClosureSelectedVanishingFunction_polarDivisor
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_sub
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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWClosureGenerator_pow_fifteen
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWFieldEquivRatFunc_X
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityFibreDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityRamificationIndex_mul_fibreDivisor_degree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWRelativeDegree_mul_fifteen
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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_finitePlaceDivisor_apply_eq_zero_of_not_mem
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalDivisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residueDegree_eq_finrank
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_IsFullConstantField_mem_range
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
private theorem sourceGaloisSelectedDivisor_selectedBaseVanishingElement_mem_maximalIdeal :
    sourceGaloisSelectedDivisor_selectedBaseVanishingElement ∈
      IsLocalRing.maximalIdeal SourceSeedBaseValuationRing := by
  rw [Valuation.mem_maximalIdeal_iff]
  exact sourceGaloisSelectedDivisor_fixedBaseOnePlace_valuation_generator_sub_one_lt_one
private theorem sourceGaloisSelectedDivisor_selectedVanishingIntegralElement_mem_upperPrime (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    sourceGaloisSelectedDivisor_selectedVanishingIntegralElement m ∈ P.1 := by
  letI : P.1.IsPrime := P.2.1
  letI : P.1.LiesOver
      (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing) := P.2.2
  change algebraMap SourceSeedBaseValuationRing
      (SourceGaloisClosureIntegralClosure m) sourceGaloisSelectedDivisor_selectedBaseVanishingElement ∈ P.1
  exact (Ideal.mem_of_liesOver (P := P.1)
    (p := IsLocalRing.maximalIdeal SourceSeedBaseValuationRing)
    sourceGaloisSelectedDivisor_selectedBaseVanishingElement).mp
      sourceGaloisSelectedDivisor_selectedBaseVanishingElement_mem_maximalIdeal
private theorem sourceGaloisSelectedDivisor_selectedVanishingIntegralElement_coe (m : ℕ) :
    ((sourceGaloisSelectedDivisor_selectedVanishingIntegralElement m : SourceGaloisClosureIntegralClosure m) :
        sourceGaloisSelectedDivisor_E m) = sourceGaloisClosureSelectedVanishingFunction m := by
  calc
    ((sourceGaloisSelectedDivisor_selectedVanishingIntegralElement m : SourceGaloisClosureIntegralClosure m) :
        sourceGaloisSelectedDivisor_E m) =
        algebraMap SourceSeedBaseValuationRing (sourceGaloisSelectedDivisor_E m)
          sourceGaloisSelectedDivisor_selectedBaseVanishingElement := by
      exact (IsScalarTower.algebraMap_apply SourceSeedBaseValuationRing
        (SourceGaloisClosureIntegralClosure m) (sourceGaloisSelectedDivisor_E m)
        sourceGaloisSelectedDivisor_selectedBaseVanishingElement).symm
    _ = algebraMap GaloisBaseField (sourceGaloisSelectedDivisor_E m)
        (AdjoinSimple.gen F256 galoisBaseZ - 1) := rfl
    _ = algebraMap GaloisBaseField (sourceGaloisSelectedDivisor_E m)
          (AdjoinSimple.gen F256 galoisBaseZ) - 1 := by
      simpa only [map_one] using
        (algebraMap GaloisBaseField (sourceGaloisSelectedDivisor_E m)).map_sub
          (AdjoinSimple.gen F256 galoisBaseZ) 1
    _ = ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : sourceGaloisSelectedDivisor_E m) ^ 15 - 1 := by
      rw [sourceGaloisWClosureGenerator_pow_fifteen]
    _ = sourceGaloisClosureSelectedVanishingFunction m :=
      (sourceGaloisClosureSelectedVanishingFunction_eq m).symm
private theorem sourceGaloisSelectedDivisor_selectedPlace_valuation_vanishingFunction_lt_one
    (m : ℕ) (j : Fin (sourceGaloisClosureSelectedLength m)) :
    (sourceGaloisClosureSelectedRationalPlace m j).place.valuation
        (sourceGaloisClosureSelectedVanishingFunction m) < 1 := by
  let P := sourceGaloisClosureSelectedPrimeEquiv m j
  let H := sourceGaloisClosureUpperHeightOne m P
  have hmem : sourceGaloisSelectedDivisor_selectedVanishingIntegralElement m ∈ H.asIdeal := by
    simpa only [H, sourceGaloisClosureUpperHeightOne_asIdeal] using
      sourceGaloisSelectedDivisor_selectedVanishingIntegralElement_mem_upperPrime m P
  have hvaluation :=
    (H.valuation_lt_one_iff_mem
      (K := sourceGaloisSelectedDivisor_E m) (sourceGaloisSelectedDivisor_selectedVanishingIntegralElement m)).mpr hmem
  change H.valuation (sourceGaloisSelectedDivisor_E m)
      (sourceGaloisClosureSelectedVanishingFunction m) < 1
  rw [← sourceGaloisSelectedDivisor_selectedVanishingIntegralElement_coe]
  exact hvaluation
private theorem sourceGaloisSelectedDivisor_selectedPlace_order_vanishingFunction_at_least_one
    (m : ℕ) (j : Fin (sourceGaloisClosureSelectedLength m)) :
    1 ≤ (sourceGaloisClosureSelectedRationalPlace m j).place.order
      (sourceGaloisClosureSelectedVanishingFunction m) := by
  have hvaluation := sourceGaloisSelectedDivisor_selectedPlace_valuation_vanishingFunction_lt_one m j
  have hvaluationNe :
      (sourceGaloisClosureSelectedRationalPlace m j).place.valuation
          (sourceGaloisClosureSelectedVanishingFunction m) ≠ 0 :=
    (sourceGaloisClosureSelectedRationalPlace m j).place.valuation.ne_zero_iff.mpr
      (sourceGaloisClosureSelectedVanishingFunction_ne_zero m)
  have hlog : WithZero.log
      ((sourceGaloisClosureSelectedRationalPlace m j).place.valuation
        (sourceGaloisClosureSelectedVanishingFunction m)) < 0 := by
    rw [← WithZero.exp_log hvaluationNe, ← WithZero.exp_zero] at hvaluation
    exact WithZero.exp_lt_exp.mp hvaluation
  unfold GlobalPlace.order
  omega
private theorem sourceGaloisSelectedDivisor_selectedVanishingFunctionZeroDivisor_apply (m : ℕ)
    (P : GlobalPlace F256 (sourceGaloisSelectedDivisor_E m)) :
    sourceGaloisSelectedDivisor_selectedVanishingFunctionZeroDivisor m P =
      max (P.order (sourceGaloisClosureSelectedVanishingFunction m)) 0 := by
  have hf := sourceGaloisClosureSelectedVanishingFunction_ne_zero m
  unfold sourceGaloisSelectedDivisor_selectedVanishingFunctionZeroDivisor
    sourceGaloisClosureSelectedVanishingFunctionPoleDivisor
  simp only [Finsupp.add_apply, GlobalPlace.principalDivisor_apply,
    Units.val_mk0, dif_neg hf, Finsupp.sup_apply,
    Finsupp.neg_apply, Finsupp.zero_apply]
  omega
private theorem sourceGaloisSelectedDivisor_selectedVanishingFunctionZeroDivisor_nonnegative (m : ℕ) :
    Divisor.Nonnegative (sourceGaloisSelectedDivisor_selectedVanishingFunctionZeroDivisor m) := by
  intro P
  rw [sourceGaloisSelectedDivisor_selectedVanishingFunctionZeroDivisor_apply]
  exact le_max_right _ _
private theorem sourceGaloisSelectedDivisor_selectedVanishingFunctionPoleDivisor_degree (m : ℕ) :
    Divisor.degree GlobalPlace.residueDegree
        (sourceGaloisClosureSelectedVanishingFunctionPoleDivisor m) =
      sourceGaloisClosureSelectedLength m := by
  rw [sourceGaloisClosureSelectedVanishingFunction_polarDivisor]
  calc
    Divisor.degree GlobalPlace.residueDegree
        ((15 * sourceGaloisWInfinityRamificationIndex m) •
          sourceGaloisWInfinityFibreDivisor m) =
        (15 * sourceGaloisWInfinityRamificationIndex m : ℕ) *
          Divisor.degree GlobalPlace.residueDegree
            (sourceGaloisWInfinityFibreDivisor m) := by
      simpa only [Divisor.degree, nsmul_eq_mul] using
        (Divisor.degreeHom GlobalPlace.residueDegree).map_nsmul
          (15 * sourceGaloisWInfinityRamificationIndex m)
          (sourceGaloisWInfinityFibreDivisor m)
    _ = (15 : ℤ) * (sourceGaloisWRelativeDegree m : ℤ) := by
      rw [Nat.cast_mul, mul_assoc,
        sourceGaloisWInfinityRamificationIndex_mul_fibreDivisor_degree]
      norm_num
    _ = sourceGaloisClosureSelectedLength m := by
      exact_mod_cast sourceGaloisWRelativeDegree_mul_fifteen m
private theorem sourceGaloisSelectedDivisor_selectedVanishingFunctionZeroDivisor_degree (m : ℕ) :
    Divisor.degree GlobalPlace.residueDegree
        (sourceGaloisSelectedDivisor_selectedVanishingFunctionZeroDivisor m) =
      sourceGaloisClosureSelectedLength m := by
  calc
    Divisor.degree GlobalPlace.residueDegree
        (sourceGaloisSelectedDivisor_selectedVanishingFunctionZeroDivisor m) =
        Divisor.degree GlobalPlace.residueDegree
            (GlobalPlace.principalDivisor (k := F256) (F := sourceGaloisSelectedDivisor_E m)
              (Units.mk0 (sourceGaloisClosureSelectedVanishingFunction m)
                (sourceGaloisClosureSelectedVanishingFunction_ne_zero m))) +
          Divisor.degree GlobalPlace.residueDegree
            (sourceGaloisClosureSelectedVanishingFunctionPoleDivisor m) := by
      rw [sourceGaloisSelectedDivisor_selectedVanishingFunctionZeroDivisor, Divisor.degree_add]
    _ = 0 + sourceGaloisClosureSelectedLength m := by
      rw [GlobalPlace.principalDivisor_degree_zero,
        sourceGaloisSelectedDivisor_selectedVanishingFunctionPoleDivisor_degree]
    _ = sourceGaloisClosureSelectedLength m := zero_add _
private theorem sourceGaloisSelectedDivisor_selectedDivisor_le_vanishingFunctionZeroDivisor (m : ℕ) :
    sourceGaloisClosureSelectedDivisor m ≤
      sourceGaloisSelectedDivisor_selectedVanishingFunctionZeroDivisor m := by
  intro P
  classical
  by_cases hP : ∃ j : Fin (sourceGaloisClosureSelectedLength m),
      (sourceGaloisClosureSelectedRationalPlace m j).place = P
  · obtain ⟨j, rfl⟩ := hP
    rw [sourceGaloisClosureSelectedDivisor_apply,
      sourceGaloisSelectedDivisor_selectedVanishingFunctionZeroDivisor_apply]
    exact (sourceGaloisSelectedDivisor_selectedPlace_order_vanishingFunction_at_least_one m j).trans
      (le_max_left _ _)
  · have hzero : sourceGaloisClosureSelectedDivisor m P = 0 := by
      unfold sourceGaloisClosureSelectedDivisor
      apply GlobalPlace.finitePlaceDivisor_apply_eq_zero_of_not_mem
      simpa only [Set.mem_range] using hP
    rw [hzero]
    exact sourceGaloisSelectedDivisor_selectedVanishingFunctionZeroDivisor_nonnegative m P
private theorem sourceGaloisSelectedDivisor_residueDegree_pos (m : ℕ) (P : GlobalPlace F256 (sourceGaloisSelectedDivisor_E m)) :
    0 < GlobalPlace.residueDegree P := by
  letI : Algebra F256 (GlobalPlace.residueField P) :=
    GlobalPlace.residueAlgebra P
  letI : FiniteDimensional F256 (GlobalPlace.residueField P) :=
    GlobalPlace.residueField_finiteDimensional P
  rw [GlobalPlace.residueDegree_eq_finrank P]
  exact Module.finrank_pos
private theorem sourceGaloisSelectedDivisor_divisor_eq_of_le_of_degree_eq (m : ℕ)
    {D R : Divisor (GlobalPlace F256 (sourceGaloisSelectedDivisor_E m))} (hDR : D ≤ R)
    (hdegree : Divisor.degree GlobalPlace.residueDegree D =
      Divisor.degree GlobalPlace.residueDegree R) :
    D = R := by
  classical
  let H : Divisor (GlobalPlace F256 (sourceGaloisSelectedDivisor_E m)) := R - D
  have hHNonnegative : Divisor.Nonnegative H := by
    intro P
    dsimp only [H]
    exact sub_nonneg.mpr (hDR P)
  have hHDegree : Divisor.degree GlobalPlace.residueDegree H = 0 := by
    dsimp only [H]
    rw [Divisor.degree_sub, hdegree, sub_self]
  have hsum :
      (∑ P ∈ H.support,
        H P * (GlobalPlace.residueDegree P : ℤ)) = 0 := by
    exact hHDegree
  have htermNonnegative :
      ∀ P ∈ H.support,
        0 ≤ H P * (GlobalPlace.residueDegree P : ℤ) := by
    intro P _
    exact mul_nonneg (hHNonnegative P) (Int.natCast_nonneg _)
  have hHzero : H = 0 := by
    apply Finsupp.ext
    intro P
    by_cases hP : P ∈ H.support
    · have hterm :=
        (Finset.sum_eq_zero_iff_of_nonneg htermNonnegative).mp hsum P hP
      have hdegreeP : (GlobalPlace.residueDegree P : ℤ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (sourceGaloisSelectedDivisor_residueDegree_pos m P))
      exact (mul_eq_zero.mp hterm).resolve_right hdegreeP
    · exact Finsupp.notMem_support_iff.mp hP
  apply Finsupp.ext
  intro P
  have hcoefficient := DFunLike.congr_fun hHzero P
  change R P - D P = 0 at hcoefficient
  omega
private theorem sourceGaloisSelectedDivisor_selectedVanishingFunctionZeroDivisor_eq_selectedDivisor
    (m : ℕ) :
    sourceGaloisSelectedDivisor_selectedVanishingFunctionZeroDivisor m =
      sourceGaloisClosureSelectedDivisor m := by
  apply Eq.symm
  apply sourceGaloisSelectedDivisor_divisor_eq_of_le_of_degree_eq m
    (sourceGaloisSelectedDivisor_selectedDivisor_le_vanishingFunctionZeroDivisor m)
  rw [sourceGaloisClosureSelectedDivisor_degree,
    sourceGaloisSelectedDivisor_selectedVanishingFunctionZeroDivisor_degree]
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
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingBaseModule
attribute [local instance 2000] sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingBaseModule
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingAlgebra
attribute [local instance 2000] sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingAlgebra
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingSMul
attribute [local instance 2000] sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingModule
attribute [local instance 2000] sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_selectedDivisorBaseScalarTower
attribute [local instance] sourceGaloisSelectedDivisor_selectedDivisorBaseScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureFractionTower
attribute [local instance] sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureFractionTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureTorsionFree
attribute [local instance] sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureTorsionFree
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureFinite
attribute [local instance] sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureIsFractionRing
attribute [local instance] sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureIsFractionRing
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureIsDedekind
attribute [local instance] sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureIsDedekind
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ)
    (j : Fin (sourceGaloisClosureSelectedLength m)) :
    (sourceGaloisClosureSelectedRationalPlace m j).place.order
        (sourceGaloisClosureSelectedVanishingFunction m) = 1 := by
  have hcoefficient := congrArg
    (fun D : Divisor (GlobalPlace F256 (sourceGaloisSelectedDivisor_E m)) =>
      D (sourceGaloisClosureSelectedRationalPlace m j).place)
    (sourceGaloisSelectedDivisor_selectedVanishingFunctionZeroDivisor_eq_selectedDivisor m)
  change sourceGaloisSelectedDivisor_selectedVanishingFunctionZeroDivisor m
      (sourceGaloisClosureSelectedRationalPlace m j).place =
    sourceGaloisClosureSelectedDivisor m
      (sourceGaloisClosureSelectedRationalPlace m j).place at hcoefficient
  rw [sourceGaloisSelectedDivisor_selectedVanishingFunctionZeroDivisor_apply,
    sourceGaloisClosureSelectedDivisor_apply] at hcoefficient
  have horder := sourceGaloisSelectedDivisor_selectedPlace_order_vanishingFunction_at_least_one m j
  rw [max_eq_left (by omega)] at hcoefficient
  exact hcoefficient
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
