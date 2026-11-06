-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSelectedRestrictedBasePlace_eq_baseOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:25:09.98713+00:00
-- url     : https://prove2.me/submissions/807a6847-5842-4d68-a816-9bd08627e240

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedPlaceOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RatFuncPlaceClassification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedBaseRestriction
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_baseRationalPlace_place_eq_rationalAdic
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceSplitIntegralCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_splitIntegralAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSplitUpperRationalPlace_place
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepResidualPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_splitUpperRationalPlace_place
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_trivialOnConstants
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_normalizedValuation_eq_of_isEquiv
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
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
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
open Polynomial
open scoped RatFunc WithZero
open MonoidWithZeroHom
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
private theorem sourceRestrictedGlobalPlace_eq_of_valuation_eq
    {P Q : GlobalPlace F256 (RatFunc F256)}
    (hvaluation : P.valuation = Q.valuation) : P = Q := by
  cases P
  cases Q
  cases hvaluation
  rfl
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open Polynomial
open scoped RatFunc WithZero
open MonoidWithZeroHom
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    sourceSelectedRestrictedBasePlace m index =
      (baseRationalPlace (1 : BasePoint)).place := by
  let P := sourceSelectedRestrictedBasePlace m index
  let v := P.valuation
  have ht : v (RatFunc.X - 1) = WithZero.exp (-1 : ℤ) :=
    sourceSelectedRestrictedBaseValuation_X_sub_one m index
  have ht_lt : v (RatFunc.X - 1) < 1 := by
    rw [ht, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  letI : v.IsNontrivial := by
    rw [Valuation.isNontrivial_iff_exists_lt_one]
    refine ⟨RatFunc.X - 1, ?_, ht_lt⟩
    apply sub_ne_zero.mpr
    intro hX
    exact RatFunc.transcendental_X (hX ▸ isAlgebraic_one)
  letI : IsCyclic (valueGroup (MonoidWithZeroHom.ofClass v)) := inferInstance
  letI : Nontrivial (valueGroup (MonoidWithZeroHom.ofClass v)) := inferInstance
  letI : v.IsRankOneDiscrete :=
    Valuation.IsRankOneDiscrete.mk' v
  letI : v.IsTrivialOn F256 := P.trivialOnConstants
  have hX : v RatFunc.X ≤ 1 := by
    have hdecomp : (RatFunc.X : RatFunc F256) =
        (RatFunc.X - 1) + 1 := by ring
    rw [hdecomp]
    exact (v.map_add (RatFunc.X - 1) 1).trans
      (max_le (le_of_lt ht_lt) (by simp))
  obtain ⟨p, hp⟩ :=
    RatFunc.valuation_isEquiv_adic_of_valuation_X_le_one (v := v) hX
  have htAdic :
      p.valuation (RatFunc F256) (RatFunc.X - 1) < 1 :=
    hp.lt_one_iff_lt_one.mp ht_lt
  have hmem :
      (Polynomial.X - Polynomial.C (1 : F256)) ∈ p.asIdeal := by
    apply (p.valuation_lt_one_iff_mem (K := RatFunc F256)
      (Polynomial.X - Polynomial.C (1 : F256))).mp
    simpa only [map_sub, RatFunc.algebraMap_X, map_one,
      RatFunc.algebraMap_eq_C] using htAdic
  have hp_eq : p = baseHeightOnePoint (1 : BasePoint) := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    have hle : (baseHeightOnePoint (1 : BasePoint)).asIdeal ≤
        p.asIdeal := by
      rw [baseHeightOnePoint_asIdeal]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
    exact ((baseHeightOnePoint (1 : BasePoint)).isMaximal.eq_of_le
      p.isPrime.ne_top hle).symm
  have hvaluation :
      P.valuation =
        (GlobalPlace.rationalAdic
          (baseHeightOnePoint (1 : BasePoint))).valuation := by
    change v = _
    rw [← hp_eq]
    exact normalizedValuation_eq_of_isEquiv
      v (p.valuation (RatFunc F256)) P.normalized
      (p.valuation_surjective (RatFunc F256)) hp
  rw [baseRationalPlace_place_eq_rationalAdic]
  exact sourceRestrictedGlobalPlace_eq_of_valuation_eq hvaluation
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
