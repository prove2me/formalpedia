-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroPlaceOfPrime_order_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:38:39.935877+00:00
-- url     : https://prove2.me/submissions/c3f494a2-39b3-4296-bad1-982d5a00fd96

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWFibres
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWGlobalPlaces
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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWClosureZeroPlace_order_generator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWFieldEquivRatFunc_X
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWZeroRamificationIndex_eq_prime
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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuation_uniformizer
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
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWFieldEquivRatFunc_X
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
attribute [local instance 3000] wClosureAlgebra
attribute [local instance 3000] wClosureSMul
attribute [local instance 3000] wClosureModule
attribute [local instance 3000] wClosureFree
attribute [local instance 3000] wBaseFree
attribute [local instance 3000] wClosureFaithfulSMul
attribute [local instance] wClosureScalarTower
attribute [local instance] wClosureTorsionFree
attribute [local instance] wClosureFiniteDimensional
attribute [local instance] wClosureIsGalois
attribute [local instance 2000] oBaseModule
attribute [local instance 2000] oBaseFaithfulSMul
attribute [local instance 2000] oClosureAlgebra
attribute [local instance 2000] oClosureSMul
attribute [local instance 2000] oClosureModule
attribute [local instance] oBaseScalarTower
attribute [local instance] oIntegralClosureFractionTower
attribute [local instance] oIntegralClosureTorsionFree
attribute [local instance] oIntegralClosureFaithfulSMul
attribute [local instance] oIntegralClosureFinite
attribute [local instance] oIntegralClosureIsFractionRing
attribute [local instance] oIntegralClosureIsDedekind
section SourceGaloisWOrderCertificate
attribute [local instance 5000]
  SubsemiringClass.toCommSemiring CommSemiring.toSemiring
  Semiring.toAddCommMonoid AddCommMonoid.toAddMonoid
  AddMonoid.toAddZeroClass AddZeroClass.toAddZero AddZero.toZero
  Zero.toOfNat0
@[simp]
private theorem coe_sourceGaloisWOrderOneElement (m : ℕ)
    (Q : GlobalPlace F256 (W m)) (x : W m) (hx : Q.order x = 1) :
    (sourceGaloisWOrderOneElement m Q x hx : W m) = x :=
  rfl
private theorem sourceGaloisWOrderOneElement_ne_zero (m : ℕ)
    (Q : GlobalPlace F256 (W m)) (x : W m) (hx : Q.order x = 1) :
    sourceGaloisWOrderOneElement m Q x hx ≠ 0 := by
  intro hzero
  apply sourceGaloisWElement_ne_zero_of_order_eq_one m Q x hx
  have hcoe := congrArg (fun y : Q.valuationRing => (y : W m)) hzero
  exact hcoe
private theorem sourceGaloisWOrderOneElement_valuation (m : ℕ)
    (Q : GlobalPlace F256 (W m)) (x : W m) (hx : Q.order x = 1) :
    Q.valuation (sourceGaloisWOrderOneElement m Q x hx : W m) =
      WithZero.exp (-1 : ℤ) := by
  have hvaluation_ne :
      Q.valuation (sourceGaloisWOrderOneElement m Q x hx : W m) ≠ 0 :=
    Q.valuation.ne_zero_iff.mpr (by
      simpa only [coe_sourceGaloisWOrderOneElement] using
        sourceGaloisWElement_ne_zero_of_order_eq_one m Q x hx)
  have hlog : WithZero.log
      (Q.valuation (sourceGaloisWOrderOneElement m Q x hx : W m)) = -1 := by
    have horder := hx
    simp only [GlobalPlace.order] at horder
    simpa only [coe_sourceGaloisWOrderOneElement] using (show
      WithZero.log (Q.valuation x) = -1 by omega)
  calc
    Q.valuation (sourceGaloisWOrderOneElement m Q x hx : W m) =
        WithZero.exp (WithZero.log
          (Q.valuation (sourceGaloisWOrderOneElement m Q x hx : W m))) :=
      (WithZero.exp_log hvaluation_ne).symm
    _ = WithZero.exp (-1 : ℤ) := by rw [hlog]
private theorem maximalIdeal_eq_span_sourceGaloisWOrderOneElement (m : ℕ)
    (Q : GlobalPlace F256 (W m)) (x : W m) (hx : Q.order x = 1) :
    IsLocalRing.maximalIdeal Q.valuationRing =
      Ideal.span ({sourceGaloisWOrderOneElement m Q x hx} :
        Set Q.valuationRing) := by
  letI : Q.valuation.IsNontrivial := by
    rw [Valuation.isNontrivial_iff_exists_lt_one]
    refine ⟨Q.uniformizer, ?_, ?_⟩
    · apply Q.valuation.ne_zero_iff.mp
      rw [Q.valuation_uniformizer]
      exact WithZero.exp_ne_zero
    · rw [Q.valuation_uniformizer, ← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by omega)
  letI : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass Q.valuation)) := inferInstance
  letI : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass Q.valuation)) := inferInstance
  letI : Q.valuation.IsRankOneDiscrete :=
    Valuation.IsRankOneDiscrete.mk' Q.valuation
  apply Valuation.IsUniformizer.is_generator
  change Q.valuation (sourceGaloisWOrderOneElement m Q x hx : W m) =
    ((Valuation.IsRankOneDiscrete.generator Q.valuation :
      (WithZero (Multiplicative ℤ))ˣ) : WithZero (Multiplicative ℤ))
  rw [sourceGaloisWOrderOneElement_valuation]
  simpa using congrArg
    (fun u : (WithZero (Multiplicative ℤ))ˣ =>
      (u : WithZero (Multiplicative ℤ)))
    (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v := Q.valuation) Q.normalized).symm
end SourceGaloisWOrderCertificate
private theorem sourceGaloisWPlaceOfHeightOne_order_integral_eq_multiplicity
    (m : ℕ) (Q : GlobalPlace F256 (W m))
    (H : IsDedekindDomain.HeightOneSpectrum (C m Q))
    {y : C m Q} (hy : y ≠ 0) :
    (sourceGaloisWPlaceOfHeightOne m Q H).order
        (algebraMap (C m Q) (E m) y) =
      (multiplicity H.asIdeal (Ideal.span {y}) : ℤ) := by
  have hvaluation :
      H.valuation (E m) (algebraMap (C m Q) (E m) y) =
        WithZero.exp (-(multiplicity H.asIdeal (Ideal.span {y}) : ℤ)) := by
    calc
      H.valuation (E m) (algebraMap (C m Q) (E m) y) =
          H.intValuation y := H.valuation_of_algebraMap y
      _ = WithZero.exp
          (-(multiplicity H.asIdeal (Ideal.span {y}) : ℤ)) :=
        H.intValuation_eq_exp_neg_multiplicity hy
  unfold GlobalPlace.order
  change -WithZero.log
      (H.valuation (E m) (algebraMap (C m Q) (E m) y)) = _
  have hlog :
      WithZero.log
          (H.valuation (E m) (algebraMap (C m Q) (E m) y)) =
        -(multiplicity H.asIdeal (Ideal.span {y}) : ℤ) :=
    (congrArg WithZero.log hvaluation).trans (WithZero.log_exp _)
  omega
private theorem algebraMap_sourceGaloisWOrderOneElement_ne_zero
    (m : ℕ) (Q : GlobalPlace F256 (W m)) (x : W m)
    (hx : Q.order x = 1) :
    algebraMap Q.valuationRing (C m Q)
        (sourceGaloisWOrderOneElement m Q x hx) ≠ 0 := by
  exact (Module.isTorsionFree_iff_algebraMap_injective.mp
    (oIntegralClosureTorsionFree m Q)).ne
      (sourceGaloisWOrderOneElement_ne_zero m Q x hx)
private theorem span_algebraMap_sourceGaloisWOrderOneElement_eq_map_maximalIdeal
    (m : ℕ) (Q : GlobalPlace F256 (W m)) (x : W m)
    (hx : Q.order x = 1) :
    Ideal.span
        ({algebraMap Q.valuationRing (C m Q)
          (sourceGaloisWOrderOneElement m Q x hx)} : Set (C m Q)) =
      Ideal.map (algebraMap Q.valuationRing (C m Q))
        (IsLocalRing.maximalIdeal Q.valuationRing) := by
  let t : Q.valuationRing := sourceGaloisWOrderOneElement m Q x hx
  let tC : C m Q := algebraMap Q.valuationRing (C m Q) t
  have hbase := maximalIdeal_eq_span_sourceGaloisWOrderOneElement m Q x hx
  calc
    Ideal.span ({tC} : Set (C m Q)) =
      Ideal.map (algebraMap Q.valuationRing (C m Q))
          (Ideal.span ({t} : Set Q.valuationRing)) := by
      symm
      simp only [Ideal.map_span, Set.image_singleton, tC]
    _ = Ideal.map (algebraMap Q.valuationRing (C m Q))
          (IsLocalRing.maximalIdeal Q.valuationRing) :=
      congrArg (Ideal.map (algebraMap Q.valuationRing (C m Q))) hbase.symm
private theorem map_sourceGaloisWMaximalIdeal_ne_bot
    (m : ℕ) (Q : GlobalPlace F256 (W m)) :
    Ideal.map (algebraMap Q.valuationRing (C m Q))
        (IsLocalRing.maximalIdeal Q.valuationRing) ≠ ⊥ := by
  letI : IsDiscreteValuationRing Q.valuationRing :=
    Q.valuationRing_isDiscreteValuationRing
  exact Ideal.map_ne_bot_of_ne_bot
    (IsDiscreteValuationRing.not_a_field Q.valuationRing)
set_option synthInstance.maxHeartbeats 100000 in
private theorem multiplicity_span_algebraMap_sourceGaloisWOrderOneElement_eq_ramificationIdx
    (m : ℕ) (Q : GlobalPlace F256 (W m))
    (H : IsDedekindDomain.HeightOneSpectrum (C m Q))
    (x : W m) (hx : Q.order x = 1) :
    multiplicity H.asIdeal
        (Ideal.span
          ({algebraMap Q.valuationRing (C m Q)
            (sourceGaloisWOrderOneElement m Q x hx)} : Set (C m Q))) =
      (IsLocalRing.maximalIdeal Q.valuationRing).ramificationIdx' H.asIdeal := by
  calc
    multiplicity H.asIdeal
        (Ideal.span
          ({algebraMap Q.valuationRing (C m Q)
            (sourceGaloisWOrderOneElement m Q x hx)} : Set (C m Q))) =
      multiplicity H.asIdeal
        (Ideal.map (algebraMap Q.valuationRing (C m Q))
          (IsLocalRing.maximalIdeal Q.valuationRing)) :=
      congrArg (multiplicity H.asIdeal)
        (span_algebraMap_sourceGaloisWOrderOneElement_eq_map_maximalIdeal m Q x hx)
    _ = (IsLocalRing.maximalIdeal Q.valuationRing).ramificationIdx' H.asIdeal :=
      (Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity
        (map_sourceGaloisWMaximalIdeal_ne_bot m Q) H.isPrime).symm
set_option synthInstance.maxHeartbeats 100000 in
private theorem sourceGaloisWPlaceOfHeightOne_order_of_order_eq_one
    (m : ℕ) (Q : GlobalPlace F256 (W m))
    (H : IsDedekindDomain.HeightOneSpectrum (C m Q))
    (x : W m) (hx : Q.order x = 1) :
    (sourceGaloisWPlaceOfHeightOne m Q H).order
        (algebraMap (W m) (E m) x) =
      ((IsLocalRing.maximalIdeal (O m Q)).ramificationIdx' H.asIdeal : ℤ) := by
  let t : Q.valuationRing := sourceGaloisWOrderOneElement m Q x hx
  let tC : C m Q := algebraMap Q.valuationRing (C m Q) t
  have htC_ne : tC ≠ 0 :=
    algebraMap_sourceGaloisWOrderOneElement_ne_zero m Q x hx
  change (sourceGaloisWPlaceOfHeightOne m Q H).order
      (algebraMap (C m Q) (E m) tC) =
    ((IsLocalRing.maximalIdeal Q.valuationRing).ramificationIdx' H.asIdeal : ℤ)
  rw [sourceGaloisWPlaceOfHeightOne_order_integral_eq_multiplicity m Q H htC_ne]
  norm_cast
  exact multiplicity_span_algebraMap_sourceGaloisWOrderOneElement_eq_ramificationIdx
    m Q H x hx
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

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
theorem _root_.solution (m : ℕ)
    (P : SourceGaloisWZeroPrime m) :
    (sourceGaloisWZeroPlaceOfPrime m P).order
        ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) :
          SourceGaloisClosureField m) =
      (sourceGaloisWZeroRamificationIndex m : ℤ) := by
  have horder := sourceGaloisWPlaceOfHeightOne_order_of_order_eq_one m
    (sourceGaloisWClosureZeroPlace m) (sourceGaloisWZeroUpperHeightOne m P)
    (sourceGaloisWClosureGenerator m)
    (sourceGaloisWClosureZeroPlace_order_generator m)
  rw [sourceGaloisWZeroRamificationIndex_eq_prime m P]
  exact horder
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
