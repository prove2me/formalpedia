-- Prove2me | solution 1 for V3AsmLevel.strict_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/11cd4794-a586-56e0-9670-d9085440400d

import Mathlib
import Definitions.Def_ModularCurve_ResolvedModelSiteLevel
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_isSeparated
import Theorems.Thm_MvPolynomial_CrossingQuotient_exists_algEquiv_quotient_span_U_and_span_V_polynomial
import Theorems.Thm_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform
import Theorems.Thm_ModularCurve_DRModelPackageLevel_preimage_closure_image_range_comp_eq_of_comp_fst_eq
import Theorems.Thm_ModularCurve_ssPlaces_nonempty
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_V3AsmLevel_strict_iso
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong"
p2m_attr_erase "simp" "ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one"
p2m_attr_erase "simp" "AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.CharPReduction.coeffRed_coeff"
p2m_attr_erase "simp" "ModularCurve.CharPReduction.redLocHom_apply"

set_option autoImplicit false
set_option maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry TopologicalSpace"

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

universe u

set_option autoImplicit false

noncomputable section

namespace MvPolynomial
p2m_export "MvPolynomial" "X map R zeroLocus ext support algebraMap_apply ringHom_ext comap vanishingIdeal algebraMap_eq C algHom_ext' algHom_ext map_id CrossingQuotient.Resolution CrossingQuotient.U CrossingQuotient.V CrossingQuotient CrossingQuotient.exists_algEquiv_quotient_span_U_and_span_V_polynomial"
p2m_open "MvPolynomial"

namespace CrossingQuotient
p2m_export "MvPolynomial.CrossingQuotient" "crossingScheme Resolution Resolution.ι Resolution.toCrossing U V U_mul_V lift lift_U lift_V resolutionChart resolutionChart_U resolutionChart_V mk mk_surjective Resolution.isSeparated exists_algEquiv_quotient_span_U_and_span_V_polynomial"
p2m_open "MvPolynomial.CrossingQuotient"

variable {W : Type*} [CommRing W] (t : W)

private theorem algHom_ext' {A : Type*} [Semiring A] [Algebra W A] {f g : CrossingQuotient W t →ₐ[W] A}
    (hU : f (U t) = g (U t)) (hV : f (V t) = g (V t)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · exact hU
  · exact hV

private theorem algebraMap_mem_span_V' : algebraMap W (CrossingQuotient W t) t ∈ Ideal.span {V t} := by
  rw [← U_mul_V]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

private theorem algebraMap_mem_span_U' : algebraMap W (CrossingQuotient W t) t ∈ Ideal.span {U t} := by
  rw [← U_mul_V]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

private abbrev strictVIdeal (e : ℕ) : Ideal (CrossingQuotient W (t ^ e)) :=
  Ideal.span {V (t ^ e), algebraMap W (CrossingQuotient W (t ^ e)) t}

private abbrev strictUIdeal (e : ℕ) : Ideal (CrossingQuotient W (t ^ e)) :=
  Ideal.span {U (t ^ e), algebraMap W (CrossingQuotient W (t ^ e)) t}

private theorem algebraMap_mem_strictVIdeal (e : ℕ) : algebraMap W (CrossingQuotient W (t ^ e)) t ∈ strictVIdeal t e :=
  Ideal.subset_span (Or.inr rfl)

private theorem algebraMap_mem_strictUIdeal (e : ℕ) : algebraMap W (CrossingQuotient W (t ^ e)) t ∈ strictUIdeal t e :=
  Ideal.subset_span (Or.inr rfl)

section chartZero

variable (e : ℕ)

private theorem strictVIdeal_le_ker (he : 0 < e) :
    strictVIdeal t e ≤
      RingHom.ker ((Ideal.Quotient.mkₐ W (Ideal.span {V t})).comp (resolutionChart t e ⟨0, he⟩)).toRingHom := by
  rw [Ideal.span_le]
  rintro a (rfl | rfl)
  ·
    rw [SetLike.mem_coe, RingHom.mem_ker]
    change Ideal.Quotient.mk _ (resolutionChart t e ⟨0, he⟩ (V (t ^ e))) = 0
    rw [resolutionChart_V, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  ·
    rw [SetLike.mem_coe, RingHom.mem_ker]
    change Ideal.Quotient.mk _ (resolutionChart t e ⟨0, he⟩ (algebraMap W _ t)) = 0
    rw [AlgHom.commutes, Ideal.Quotient.eq_zero_iff_mem]
    exact algebraMap_mem_span_V' t

private def strictZeroHom (he : 0 < e) :
    (CrossingQuotient W (t ^ e) ⧸ strictVIdeal t e) →ₐ[W] (CrossingQuotient W t ⧸ Ideal.span {V t}) :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ W (Ideal.span {V t})).comp (resolutionChart t e ⟨0, he⟩))
    (fun _ ha => (RingHom.mem_ker).mp (strictVIdeal_le_ker t e he ha))

private theorem strictZeroHom_mk (he : 0 < e) (a : CrossingQuotient W (t ^ e)) :
    strictZeroHom t e he (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (resolutionChart t e ⟨0, he⟩ a) := rfl

private theorem mk_algebraMap_eq_zero : Ideal.Quotient.mk (strictVIdeal t e) (algebraMap W _ t) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (algebraMap_mem_strictVIdeal t e)

private theorem quot_mul_zero (x : CrossingQuotient W (t ^ e) ⧸ strictVIdeal t e) : x * 0 = 0 := mul_zero x

private theorem mk_U_mul_zero :
    Ideal.Quotient.mk (strictVIdeal t e) (U (t ^ e)) * 0 =
      Ideal.Quotient.mk (strictVIdeal t e) (algebraMap W (CrossingQuotient W (t ^ e)) t) := by
  rw [quot_mul_zero, mk_algebraMap_eq_zero]

private def strictZeroInv :
    (CrossingQuotient W t ⧸ Ideal.span {V t}) →ₐ[W] (CrossingQuotient W (t ^ e) ⧸ strictVIdeal t e) :=
  Ideal.Quotient.liftₐ _ (lift t (Ideal.Quotient.mk _ (U (t ^ e))) 0 (mk_U_mul_zero t e))
    (by
      intro a ha
      rw [Ideal.mem_span_singleton'] at ha
      obtain ⟨b, rfl⟩ := ha
      rw [map_mul, lift_V]
      exact quot_mul_zero t e _)

private theorem strictZeroInv_mk_U :
    strictZeroInv t e (Ideal.Quotient.mk _ (U t)) = Ideal.Quotient.mk _ (U (t ^ e)) := by
  change lift t (Ideal.Quotient.mk _ (U (t ^ e))) 0 (mk_U_mul_zero t e) (U t) = _
  rw [lift_U]

private theorem strictZeroInv_mk_V : strictZeroInv t e (Ideal.Quotient.mk _ (V t)) = 0 := by
  change lift t (Ideal.Quotient.mk _ (U (t ^ e))) 0 (mk_U_mul_zero t e) (V t) = _
  rw [lift_V]

private theorem strictZeroInv_comp_strictZeroHom (he : 0 < e) :
    (strictZeroInv t e).comp (strictZeroHom t e he) = AlgHom.id W _ := by
  apply Ideal.Quotient.algHom_ext
  apply algHom_ext' (t ^ e)
  · change strictZeroInv t e (strictZeroHom t e he (Ideal.Quotient.mk _ (U (t ^ e)))) = Ideal.Quotient.mk _ (U (t ^ e))
    rw [strictZeroHom_mk, resolutionChart_U]
    simp only [pow_zero, map_one, one_mul]
    exact strictZeroInv_mk_U t e
  · change strictZeroInv t e (strictZeroHom t e he (Ideal.Quotient.mk _ (V (t ^ e)))) = Ideal.Quotient.mk _ (V (t ^ e))
    rw [strictZeroHom_mk, resolutionChart_V, map_mul, map_mul, strictZeroInv_mk_V]
    rw [quot_mul_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Or.inl rfl)

private theorem strictZeroHom_comp_strictZeroInv (he : 0 < e) :
    (strictZeroHom t e he).comp (strictZeroInv t e) = AlgHom.id W _ := by
  apply Ideal.Quotient.algHom_ext
  apply algHom_ext' t
  · change strictZeroHom t e he (strictZeroInv t e (Ideal.Quotient.mk _ (U t))) = Ideal.Quotient.mk _ (U t)
    rw [strictZeroInv_mk_U, strictZeroHom_mk, resolutionChart_U]
    simp only [pow_zero, map_one, one_mul]
  · change strictZeroHom t e he (strictZeroInv t e (Ideal.Quotient.mk _ (V t))) = Ideal.Quotient.mk _ (V t)
    rw [strictZeroInv_mk_V, map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl

private def strictZeroEquiv (he : 0 < e) :
    (CrossingQuotient W (t ^ e) ⧸ strictVIdeal t e) ≃ₐ[W] (CrossingQuotient W t ⧸ Ideal.span {V t}) :=
  AlgEquiv.ofAlgHom (strictZeroHom t e he) (strictZeroInv t e)
    (strictZeroHom_comp_strictZeroInv t e he) (strictZeroInv_comp_strictZeroHom t e he)

private theorem exists_algEquiv_comp_mk_eq_mk_comp_resolutionChart_zero (he : 0 < e) :
    ∃ E : (CrossingQuotient W (t ^ e) ⧸ strictVIdeal t e) ≃ₐ[W] (CrossingQuotient W t ⧸ Ideal.span {V t}),
      E.toAlgHom.comp (Ideal.Quotient.mkₐ W _) =
        (Ideal.Quotient.mkₐ W (Ideal.span {V t})).comp (resolutionChart t e ⟨0, he⟩) :=
  ⟨strictZeroEquiv t e he, Ideal.Quotient.algHom_ext _ rfl⟩

private theorem mk_comp_resolutionChart_zero_surjective (he : 0 < e) :
    Function.Surjective ((Ideal.Quotient.mkₐ W (Ideal.span {V t})).comp (resolutionChart t e ⟨0, he⟩)) := by
  intro z
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((strictZeroEquiv t e he).symm z)
  refine ⟨a, ?_⟩
  change (strictZeroEquiv t e he) (Ideal.Quotient.mk _ a) = z
  rw [ha, AlgEquiv.apply_symm_apply]

private theorem ker_mk_comp_resolutionChart_zero (he : 0 < e) :
    RingHom.ker ((Ideal.Quotient.mkₐ W (Ideal.span {V t})).comp (resolutionChart t e ⟨0, he⟩)).toRingHom =
      strictVIdeal t e := by
  apply le_antisymm _ (strictVIdeal_le_ker t e he)
  intro a ha
  rw [RingHom.mem_ker] at ha
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply (strictZeroEquiv t e he).injective
  rw [map_zero]
  exact ha

end chartZero

section chartLast

variable (e : ℕ)

private abbrev lastIdx (he : 0 < e) : Fin e := ⟨e - 1, Nat.sub_one_lt_of_lt he⟩

private theorem resolutionChart_last_V (he : 0 < e) : resolutionChart t e (lastIdx e he) (V (t ^ e)) = V t := by
  rw [resolutionChart_V]
  simp only [Nat.sub_self, pow_zero, map_one, one_mul]

private theorem strictUIdeal_le_ker (he : 0 < e) :
    strictUIdeal t e ≤
      RingHom.ker ((Ideal.Quotient.mkₐ W (Ideal.span {U t})).comp (resolutionChart t e (lastIdx e he))).toRingHom := by
  rw [Ideal.span_le]
  rintro a (rfl | rfl)
  ·
    rw [SetLike.mem_coe, RingHom.mem_ker]
    change Ideal.Quotient.mk _ (resolutionChart t e (lastIdx e he) (U (t ^ e))) = 0
    rw [resolutionChart_U, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  ·
    rw [SetLike.mem_coe, RingHom.mem_ker]
    change Ideal.Quotient.mk _ (resolutionChart t e (lastIdx e he) (algebraMap W _ t)) = 0
    rw [AlgHom.commutes, Ideal.Quotient.eq_zero_iff_mem]
    exact algebraMap_mem_span_U' t

private def strictLastHom (he : 0 < e) :
    (CrossingQuotient W (t ^ e) ⧸ strictUIdeal t e) →ₐ[W] (CrossingQuotient W t ⧸ Ideal.span {U t}) :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ W (Ideal.span {U t})).comp (resolutionChart t e (lastIdx e he)))
    (fun _ ha => (RingHom.mem_ker).mp (strictUIdeal_le_ker t e he ha))

private theorem strictLastHom_mk (he : 0 < e) (a : CrossingQuotient W (t ^ e)) :
    strictLastHom t e he (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (resolutionChart t e (lastIdx e he) a) := rfl

private theorem mk_algebraMap_eq_zero' : Ideal.Quotient.mk (strictUIdeal t e) (algebraMap W _ t) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (algebraMap_mem_strictUIdeal t e)

private theorem quot_zero_mul (x : CrossingQuotient W (t ^ e) ⧸ strictUIdeal t e) : 0 * x = 0 := zero_mul x

private theorem quot_mul_zero' (x : CrossingQuotient W (t ^ e) ⧸ strictUIdeal t e) : x * 0 = 0 := mul_zero x

private theorem zero_mul_mk_V :
    0 * Ideal.Quotient.mk (strictUIdeal t e) (V (t ^ e)) =
      Ideal.Quotient.mk (strictUIdeal t e) (algebraMap W (CrossingQuotient W (t ^ e)) t) := by
  rw [quot_zero_mul, mk_algebraMap_eq_zero']

private def strictLastInv :
    (CrossingQuotient W t ⧸ Ideal.span {U t}) →ₐ[W] (CrossingQuotient W (t ^ e) ⧸ strictUIdeal t e) :=
  Ideal.Quotient.liftₐ _ (lift t 0 (Ideal.Quotient.mk _ (V (t ^ e))) (zero_mul_mk_V t e))
    (by
      intro a ha
      rw [Ideal.mem_span_singleton'] at ha
      obtain ⟨b, rfl⟩ := ha
      rw [map_mul, lift_U]
      exact quot_mul_zero' t e _)

private theorem strictLastInv_mk_V :
    strictLastInv t e (Ideal.Quotient.mk _ (V t)) = Ideal.Quotient.mk _ (V (t ^ e)) := by
  change lift t 0 (Ideal.Quotient.mk _ (V (t ^ e))) (zero_mul_mk_V t e) (V t) = _
  rw [lift_V]

private theorem strictLastInv_mk_U : strictLastInv t e (Ideal.Quotient.mk _ (U t)) = 0 := by
  change lift t 0 (Ideal.Quotient.mk _ (V (t ^ e))) (zero_mul_mk_V t e) (U t) = _
  rw [lift_U]

private theorem strictLastInv_comp_strictLastHom (he : 0 < e) :
    (strictLastInv t e).comp (strictLastHom t e he) = AlgHom.id W _ := by
  apply Ideal.Quotient.algHom_ext
  apply algHom_ext' (t ^ e)
  · change strictLastInv t e (strictLastHom t e he (Ideal.Quotient.mk _ (U (t ^ e)))) = Ideal.Quotient.mk _ (U (t ^ e))
    rw [strictLastHom_mk, resolutionChart_U, map_mul, map_mul, strictLastInv_mk_U, quot_mul_zero', eq_comm,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Or.inl rfl)
  · change strictLastInv t e (strictLastHom t e he (Ideal.Quotient.mk _ (V (t ^ e)))) = Ideal.Quotient.mk _ (V (t ^ e))
    rw [strictLastHom_mk, resolutionChart_last_V]
    exact strictLastInv_mk_V t e

private theorem strictLastHom_comp_strictLastInv (he : 0 < e) :
    (strictLastHom t e he).comp (strictLastInv t e) = AlgHom.id W _ := by
  apply Ideal.Quotient.algHom_ext
  apply algHom_ext' t
  · change strictLastHom t e he (strictLastInv t e (Ideal.Quotient.mk _ (U t))) = Ideal.Quotient.mk _ (U t)
    rw [strictLastInv_mk_U, map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  · change strictLastHom t e he (strictLastInv t e (Ideal.Quotient.mk _ (V t))) = Ideal.Quotient.mk _ (V t)
    rw [strictLastInv_mk_V, strictLastHom_mk, resolutionChart_last_V]

private def strictLastEquiv (he : 0 < e) :
    (CrossingQuotient W (t ^ e) ⧸ strictUIdeal t e) ≃ₐ[W] (CrossingQuotient W t ⧸ Ideal.span {U t}) :=
  AlgEquiv.ofAlgHom (strictLastHom t e he) (strictLastInv t e)
    (strictLastHom_comp_strictLastInv t e he) (strictLastInv_comp_strictLastHom t e he)

private theorem exists_algEquiv_comp_mk_eq_mk_comp_resolutionChart_last (he : 0 < e) :
    ∃ E : (CrossingQuotient W (t ^ e) ⧸ strictUIdeal t e) ≃ₐ[W] (CrossingQuotient W t ⧸ Ideal.span {U t}),
      E.toAlgHom.comp (Ideal.Quotient.mkₐ W _) =
        (Ideal.Quotient.mkₐ W (Ideal.span {U t})).comp (resolutionChart t e (lastIdx e he)) :=
  ⟨strictLastEquiv t e he, Ideal.Quotient.algHom_ext _ rfl⟩

private theorem mk_comp_resolutionChart_last_surjective (he : 0 < e) :
    Function.Surjective ((Ideal.Quotient.mkₐ W (Ideal.span {U t})).comp (resolutionChart t e (lastIdx e he))) := by
  intro z
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((strictLastEquiv t e he).symm z)
  refine ⟨a, ?_⟩
  change (strictLastEquiv t e he) (Ideal.Quotient.mk _ a) = z
  rw [ha, AlgEquiv.apply_symm_apply]

private theorem ker_mk_comp_resolutionChart_last (he : 0 < e) :
    RingHom.ker ((Ideal.Quotient.mkₐ W (Ideal.span {U t})).comp (resolutionChart t e (lastIdx e he))).toRingHom =
      strictUIdeal t e := by
  apply le_antisymm _ (strictUIdeal_le_ker t e he)
  intro a ha
  rw [RingHom.mem_ker] at ha
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply (strictLastEquiv t e he).injective
  rw [map_zero]
  exact ha

end chartLast

end CrossingQuotient

end MvPolynomial

end

noncomputable section

namespace MvPolynomial
p2m_export "MvPolynomial" "X map R zeroLocus ext support algebraMap_apply ringHom_ext comap vanishingIdeal algebraMap_eq C algHom_ext' algHom_ext map_id CrossingQuotient.Resolution CrossingQuotient.U CrossingQuotient.V CrossingQuotient CrossingQuotient.exists_algEquiv_quotient_span_U_and_span_V_polynomial"
namespace CrossingQuotient
p2m_export "MvPolynomial.CrossingQuotient" "crossingScheme Resolution Resolution.ι Resolution.toCrossing U V U_mul_V lift lift_U lift_V resolutionChart resolutionChart_U resolutionChart_V mk mk_surjective Resolution.isSeparated exists_algEquiv_quotient_span_U_and_span_V_polynomial"
namespace Resolution
p2m_export "MvPolynomial.CrossingQuotient.Resolution" "ι openCover toCrossing ι_toCrossing toSpec ι_toSpec hom_ext isSeparated"
p2m_open "MvPolynomial.CrossingQuotient.Resolution MvPolynomial.CrossingQuotient MvPolynomial"

p2m_open "AlgebraicGeometry P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry CategoryTheory"

universe v

variable {W : Type v} [CommRing W] (t : W) (e : ℕ)

private theorem isSeparated_toCrossing' : IsSeparated (Resolution.toCrossing t e) :=
  (Resolution.isSeparated t e).2

private def strictVι (he : 0 < e) :
    Spec (CommRingCat.of (CrossingQuotient W t ⧸ Ideal.span {V t})) ⟶ Resolution t e :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {V t}))) ≫ Resolution.ι t e ⟨0, he⟩

private def strictUι (he : 0 < e) :
    Spec (CommRingCat.of (CrossingQuotient W t ⧸ Ideal.span {U t})) ⟶ Resolution t e :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {U t}))) ≫ Resolution.ι t e (lastIdx e he)

private theorem strictVι_toCrossing (he : 0 < e) :
    strictVι t e he ≫ toCrossing t e = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mkₐ W (Ideal.span {V t})).comp (resolutionChart t e ⟨0, he⟩)).toRingHom) := by
  rw [strictVι, Category.assoc, ι_toCrossing, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

private theorem strictUι_toCrossing (he : 0 < e) :
    strictUι t e he ≫ toCrossing t e = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mkₐ W (Ideal.span {U t})).comp (resolutionChart t e (lastIdx e he))).toRingHom) := by
  rw [strictUι, Category.assoc, ι_toCrossing, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

private scoped instance isClosedImmersion_strictVι_toCrossing (he : 0 < e) : IsClosedImmersion (strictVι t e he ≫ toCrossing t e) := by
  rw [strictVι_toCrossing]
  exact IsClosedImmersion.spec_of_surjective _ (mk_comp_resolutionChart_zero_surjective t e he)

private scoped instance isClosedImmersion_strictUι_toCrossing (he : 0 < e) : IsClosedImmersion (strictUι t e he ≫ toCrossing t e) := by
  rw [strictUι_toCrossing]
  exact IsClosedImmersion.spec_of_surjective _ (mk_comp_resolutionChart_last_surjective t e he)

private scoped instance isClosedImmersion_strictVι (he : 0 < e) : IsClosedImmersion (strictVι t e he) :=
  haveI := isSeparated_toCrossing' t e
  IsClosedImmersion.of_comp (strictVι t e he) (toCrossing t e)

private scoped instance isClosedImmersion_strictUι (he : 0 < e) : IsClosedImmersion (strictUι t e he) :=
  haveI := isSeparated_toCrossing' t e
  IsClosedImmersion.of_comp (strictUι t e he) (toCrossing t e)

private theorem range_strictVι_toCrossing (he : 0 < e) :
    Set.range (strictVι t e he ≫ toCrossing t e).base = PrimeSpectrum.zeroLocus (strictVIdeal t e : Set (CrossingQuotient W (t ^ e))) := by
  rw [strictVι_toCrossing, ← ker_mk_comp_resolutionChart_zero t e he, Spec.map_base]
  exact _root_.range_comap_of_surjective _ _ (mk_comp_resolutionChart_zero_surjective t e he)

private theorem range_strictUι_toCrossing (he : 0 < e) :
    Set.range (strictUι t e he ≫ toCrossing t e).base = PrimeSpectrum.zeroLocus (strictUIdeal t e : Set (CrossingQuotient W (t ^ e))) := by
  rw [strictUι_toCrossing, ← ker_mk_comp_resolutionChart_last t e he, Spec.map_base]
  exact _root_.range_comap_of_surjective _ _ (mk_comp_resolutionChart_last_surjective t e he)

private theorem mem_zeroLocus_strictVIdeal_iff (P : PrimeSpectrum (CrossingQuotient W (t ^ e))) :
    P ∈ PrimeSpectrum.zeroLocus (strictVIdeal t e : Set (CrossingQuotient W (t ^ e))) ↔
      V (t ^ e) ∈ P.asIdeal ∧ algebraMap W _ t ∈ P.asIdeal := by
  rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  rfl

private theorem mem_zeroLocus_strictUIdeal_iff (P : PrimeSpectrum (CrossingQuotient W (t ^ e))) :
    P ∈ PrimeSpectrum.zeroLocus (strictUIdeal t e : Set (CrossingQuotient W (t ^ e))) ↔
      U (t ^ e) ∈ P.asIdeal ∧ algebraMap W _ t ∈ P.asIdeal := by
  rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  rfl

private theorem algebraMap_mem_of_V_mem (P : PrimeSpectrum (CrossingQuotient W (t ^ e)))
    (hV : V (t ^ e) ∈ P.asIdeal) : algebraMap W _ t ∈ P.asIdeal := by
  apply P.isPrime.mem_of_pow_mem e
  rw [← map_pow, ← U_mul_V]
  exact P.asIdeal.mul_mem_left _ hV

private theorem algebraMap_mem_of_U_mem (P : PrimeSpectrum (CrossingQuotient W (t ^ e)))
    (hU : U (t ^ e) ∈ P.asIdeal) : algebraMap W _ t ∈ P.asIdeal := by
  apply P.isPrime.mem_of_pow_mem e
  rw [← map_pow, ← U_mul_V]
  exact P.asIdeal.mul_mem_right _ hU

private theorem mem_range_strictVι_toCrossing_iff (he : 0 < e) (P : PrimeSpectrum (CrossingQuotient W (t ^ e))) :
    P ∈ Set.range (strictVι t e he ≫ toCrossing t e).base ↔ V (t ^ e) ∈ P.asIdeal := by
  have h1 : P ∈ Set.range (strictVι t e he ≫ toCrossing t e).base ↔
      P ∈ PrimeSpectrum.zeroLocus (strictVIdeal t e : Set (CrossingQuotient W (t ^ e))) := by
    rw [range_strictVι_toCrossing]
    exact Iff.rfl
  exact h1.trans ((mem_zeroLocus_strictVIdeal_iff t e P).trans
    ⟨fun h => h.1, fun h => ⟨h, algebraMap_mem_of_V_mem t e P h⟩⟩)

private theorem mem_range_strictUι_toCrossing_iff (he : 0 < e) (P : PrimeSpectrum (CrossingQuotient W (t ^ e))) :
    P ∈ Set.range (strictUι t e he ≫ toCrossing t e).base ↔ U (t ^ e) ∈ P.asIdeal := by
  have h1 : P ∈ Set.range (strictUι t e he ≫ toCrossing t e).base ↔
      P ∈ PrimeSpectrum.zeroLocus (strictUIdeal t e : Set (CrossingQuotient W (t ^ e))) := by
    rw [range_strictUι_toCrossing]
    exact Iff.rfl
  exact h1.trans ((mem_zeroLocus_strictUIdeal_iff t e P).trans
    ⟨fun h => h.1, fun h => ⟨h, algebraMap_mem_of_U_mem t e P h⟩⟩)

end MvPolynomial.CrossingQuotient.Resolution
p2m_reactivate "P2MW.S_V3AsmLevel_strict_iso.MvPolynomial P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient.Resolution"
p2m_reactivate "P2MW.S_V3AsmLevel_strict_iso.MvPolynomial P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient"
p2m_reactivate "P2MW.S_V3AsmLevel_strict_iso.MvPolynomial"

end
p2m_reactivate "P2MW.S_V3AsmLevel_strict_iso.MvPolynomial P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient.Resolution"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective IsClosedImmersion.of_comp basicOpen_eq_bot_iff Scheme.Hom iSup_affineOpens_eq_top Scheme.Pullback.range_fst LocallyOfFiniteType Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme pullbackSpecIso Spec.map_base Scheme.Hom.comp_base IsReduced.of_openCover Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced IsSeparated HasRingHomProperty.appLE SpecMap_ΓSpecIso_hom isAffineOpen_top Scheme.preimage_basicOpen_top Spec.map_id Etale Scheme.Spec affine_isIntegral_iff FormallyUnramified isReduced_of_isOpenImmersion isReduced_of_isAffine_isReduced HasRingHomProperty Etale.iff_flat_and_formallyUnramified toSpecΓ Scheme.Hom.comp_apply basicOpen_eq_of_affine geometrically range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso"
p2m_open "AlgebraicGeometry"

section monoPullback

variable {C : Type*} [Category C] {S A B Z : C} (s : S ⟶ B) (a : A ⟶ B) (i : B ⟶ Z) [Mono i]
  [HasPullback s a] [HasPullback (s ≫ i) (a ≫ i)]

private noncomputable def pullbackCompMonoIso : pullback (s ≫ i) (a ≫ i) ≅ pullback s a where
  hom := pullback.lift (pullback.fst _ _) (pullback.snd _ _)
    ((cancel_mono i).mp (by simpa only [Category.assoc] using pullback.condition))
  inv := pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by rw [pullback.condition_assoc])
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]

@[scoped simp, reassoc]
private theorem pullbackCompMonoIso_hom_fst : (pullbackCompMonoIso s a i).hom ≫ pullback.fst s a = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

@[scoped simp, reassoc]
private theorem pullbackCompMonoIso_hom_snd : (pullbackCompMonoIso s a i).hom ≫ pullback.snd s a = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

@[scoped simp, reassoc]
private theorem pullbackCompMonoIso_inv_fst : (pullbackCompMonoIso s a i).inv ≫ pullback.fst _ _ = pullback.fst s a :=
  pullback.lift_fst _ _ _

@[scoped simp, reassoc]
private theorem pullbackCompMonoIso_inv_snd : (pullbackCompMonoIso s a i).inv ≫ pullback.snd _ _ = pullback.snd s a :=
  pullback.lift_snd _ _ _

end monoPullback
p2m_reactivate "P2MW.S_V3AsmLevel_strict_iso.MvPolynomial P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient.Resolution"

private theorem flat_pullback_fst_comp_mono {S A B Z : Scheme.{u}} (s : S ⟶ B) (a : A ⟶ B) (i : B ⟶ Z) [Mono i] [Flat a] :
    Flat (pullback.fst (s ≫ i) (a ≫ i)) := by
  rw [← pullbackCompMonoIso_hom_fst s a i]
  infer_instance

section factor

variable {S : Scheme.{u}} {O : Type u} [CommRing O] (f : S ⟶ Spec (CommRingCat.of O)) (I : Ideal O)

private noncomputable def toΓ : O →+* Γ(S, ⊤) :=
  (f.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom

private theorem toΓ_apply (r : O) : toΓ f r = f.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv r) := rfl

private theorem toΓ_eq_zero_of_preimage_basicOpen_eq_bot [IsReduced S] (r : O)
    (hr : f ⁻¹ᵁ (PrimeSpectrum.basicOpen r : (Spec (CommRingCat.of O)).Opens) = ⊥) : toΓ f r = 0 := by
  rw [← basicOpen_eq_bot_iff, toΓ_apply, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  exact hr

variable (hI : ∀ r ∈ I, f ⁻¹ᵁ (PrimeSpectrum.basicOpen r : (Spec (CommRingCat.of O)).Opens) = ⊥)

include hI in

private theorem exists_lift_specQuotient [IsReduced S] :
    ∃ f' : S ⟶ Spec (CommRingCat.of (O ⧸ I)),
      f' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = f := by
  have hker : ∀ r ∈ I, toΓ f r = 0 := fun r hr => toΓ_eq_zero_of_preimage_basicOpen_eq_bot f r (hI r hr)
  let φ : O ⧸ I →+* Γ(S, ⊤) := Ideal.Quotient.lift I (toΓ f) hker
  refine ⟨S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ), ?_⟩
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.lift_comp_mk]

  rw [toΓ, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, CommRingCat.ofHom_hom, Spec.map_comp, ← Category.assoc,
    ← Scheme.toSpecΓ_naturality f, Category.assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.comp_id]

end factor
p2m_reactivate "P2MW.S_V3AsmLevel_strict_iso.MvPolynomial P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient.Resolution"

end AlgebraicGeometry
p2m_reactivate "P2MW.S_V3AsmLevel_strict_iso.MvPolynomial P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry"

p2m_open "AlgebraicGeometry P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry CategoryTheory TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective IsClosedImmersion.of_comp basicOpen_eq_bot_iff Scheme.Hom iSup_affineOpens_eq_top Scheme.Pullback.range_fst LocallyOfFiniteType Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme pullbackSpecIso Spec.map_base Scheme.Hom.comp_base IsReduced.of_openCover Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced IsSeparated HasRingHomProperty.appLE SpecMap_ΓSpecIso_hom isAffineOpen_top Scheme.preimage_basicOpen_top Spec.map_id Etale Scheme.Spec affine_isIntegral_iff FormallyUnramified isReduced_of_isOpenImmersion isReduced_of_isAffine_isReduced HasRingHomProperty Etale.iff_flat_and_formallyUnramified toSpecΓ Scheme.Hom.comp_apply basicOpen_eq_of_affine geometrically range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "mem_basicOpen Hom mk Γ Pullback.range_fst topIso IdealSheafData.range_subschemeι toSpecΓ_naturality Hom.comp_base zeroLocus affineOpens basicOpen preimage_basicOpen_top openCoverOfIsOpenCover Opens residue homOfLE_ι Hom.comp_apply IdealSheafData ΓSpecIso toSpecΓ"
namespace IdealSheafData
p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "radical mk map subscheme range_subschemeι map_id vanishingIdeal vanishingIdeal_ideal ideal map_comp subschemeι comap subschemeCover support"
p2m_open "AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}}

private theorem isReduced_Spec_of_isReduced (R : Type u) [CommRing R] [_root_.IsReduced R] :
    IsReduced (Spec (CommRingCat.of R)) := by
  haveI : _root_.IsReduced Γ(Spec (CommRingCat.of R), ⊤) :=
    isReduced_of_injective (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isAffine_isReduced _

private theorem isReduced_subscheme_of_isRadical (I : X.IdealSheafData)
    (hI : ∀ U : X.affineOpens, (I.ideal U).IsRadical) : IsReduced I.subscheme := by
  haveI : ∀ i, IsReduced (I.subschemeCover.openCover.X i) := fun (U : X.affineOpens) => by
    change IsReduced (Spec (CommRingCat.of (Γ(X, (U : X.Opens)) ⧸ I.ideal U)))
    haveI : _root_.IsReduced (Γ(X, (U : X.Opens)) ⧸ I.ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp (hI U)
    exact isReduced_Spec_of_isReduced _
  exact IsReduced.of_openCover _ I.subschemeCover.openCover

private scoped instance isReduced_subscheme_vanishingIdeal (Z : Closeds X) : IsReduced (vanishingIdeal Z).subscheme :=
  isReduced_subscheme_of_isRadical _ fun U => by
    rw [vanishingIdeal_ideal]
    exact PrimeSpectrum.isRadical_vanishingIdeal _

end AlgebraicGeometry.Scheme.IdealSheafData
p2m_reactivate "P2MW.S_V3AsmLevel_strict_iso.MvPolynomial P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme.IdealSheafData"
p2m_reactivate "P2MW.S_V3AsmLevel_strict_iso.MvPolynomial P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_V3AsmLevel_strict_iso.MvPolynomial P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective IsClosedImmersion.of_comp basicOpen_eq_bot_iff Scheme.Hom iSup_affineOpens_eq_top Scheme.Pullback.range_fst LocallyOfFiniteType Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme pullbackSpecIso Spec.map_base Scheme.Hom.comp_base IsReduced.of_openCover Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced IsSeparated HasRingHomProperty.appLE SpecMap_ΓSpecIso_hom isAffineOpen_top Scheme.preimage_basicOpen_top Spec.map_id Etale Scheme.Spec affine_isIntegral_iff FormallyUnramified isReduced_of_isOpenImmersion isReduced_of_isAffine_isReduced HasRingHomProperty Etale.iff_flat_and_formallyUnramified toSpecΓ Scheme.Hom.comp_apply basicOpen_eq_of_affine geometrically range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso"
p2m_open "AlgebraicGeometry"

private theorem range_specMap_of_ker_eq_maximalIdeal {O κ : Type u} [CommRing O] [IsLocalRing O] [Field κ]
    (φ : O →+* κ) (hker : RingHom.ker φ = IsLocalRing.maximalIdeal O) :
    Set.range (Spec.map (CommRingCat.ofHom φ)).base = {IsLocalRing.closedPoint O} := by
  have key : ∀ y : PrimeSpectrum κ, (Spec.map (CommRingCat.ofHom φ)).base y = IsLocalRing.closedPoint O := by
    intro y
    apply PrimeSpectrum.ext
    have hy : y.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    change Ideal.comap φ y.asIdeal = IsLocalRing.maximalIdeal O
    rw [hy, ← RingHom.ker_eq_comap_bot, hker]
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨⟨⊥, Ideal.isPrime_bot⟩, key _⟩, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact key y

private theorem IsPullback.range_fst' {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) : Set.range fst.base = f.base ⁻¹' Set.range g.base := by
  have hsurj : Function.Surjective h.isoPullback.hom.base := h.isoPullback.hom.homeomorph.surjective
  rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr hsurj, Set.image_univ, Scheme.Pullback.range_fst]

private theorem closure_subset_preimage_singleton {X B : Scheme.{u}} (π : X ⟶ B) {s : Set X} {b : B}
    (hb : IsClosed ({b} : Set B)) (hs : s ⊆ π.base ⁻¹' {b}) : closure s ⊆ π.base ⁻¹' {b} :=
  closure_minimal hs (hb.preimage π.continuous)

private theorem preimage_basicOpen_eq_bot_of_forall_eq_closedPoint {S : Scheme.{u}} {O : Type u} [CommRing O] [IsLocalRing O]
    (f : S ⟶ Spec (CommRingCat.of O)) (hf : ∀ s : S, f.base s = IsLocalRing.closedPoint O) (r : O)
    (hr : r ∈ IsLocalRing.maximalIdeal O) :
    f ⁻¹ᵁ (PrimeSpectrum.basicOpen r : (Spec (CommRingCat.of O)).Opens) = ⊥ := by
  ext s
  simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro hs
  have hs' : f.base s ∈ PrimeSpectrum.basicOpen r := hs
  rw [hf s] at hs'
  exact (PrimeSpectrum.mem_basicOpen _ _).mp hs' hr

private theorem forall_comp_eq_of_range_eq_closure {S Y B : Scheme.{u}} (ιS : S ⟶ Y) (g : Y ⟶ B) {y : Y} {b : B}
    (hS : Set.range ιS.base = closure {y}) (hy : g.base y = b) (hb : IsClosed ({b} : Set B)) (s : S) :
    (ιS ≫ g).base s = b := by
  have h1 : closure {y} ⊆ g.base ⁻¹' {b} :=
    closure_subset_preimage_singleton g hb (by rintro _ rfl; exact hy)
  have h2 : ιS.base s ∈ closure {y} := by rw [← hS]; exact ⟨s, rfl⟩
  exact h1 h2

end AlgebraicGeometry
p2m_reactivate "P2MW.S_V3AsmLevel_strict_iso.MvPolynomial P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme.IdealSheafData"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry TopologicalSpace"

namespace Algebra
p2m_export "Algebra" "EssFiniteType commutes FormallyUnramified.of_restrictScalars mk algebraMap FormallyUnramified algebraMapSubmonoid TensorProduct.comm FiniteType Etale smul_def EssFiniteType.of_comp id coe_bot FormallyUnramified.isReduced_of_field"
p2m_open "Algebra"

private theorem mem_nonZeroDivisors_algebraMap_of_flat (D B : Type*) [CommRing D] [CommRing B] [Algebra D B]
    [Module.Flat D B] {r : D} (hr : r ∈ nonZeroDivisors D) : algebraMap D B r ∈ nonZeroDivisors B := by
  have hsm : IsSMulRegular B r := Module.Flat.isSMulRegular_of_nonZeroDivisors hr
  have key : ∀ x : B, algebraMap D B r * x = 0 → x = 0 := fun x hx =>
    hsm ((Algebra.smul_def r x).trans (hx.trans (smul_zero r).symm))
  exact mem_nonZeroDivisors_iff.mpr ⟨key, fun x hx => key x ((mul_comm _ _).trans hx)⟩

private theorem isReduced_of_flat_of_formallyUnramified_of_isDomain (D B : Type*) [CommRing D] [IsDomain D]
    [CommRing B] [Algebra D B] [Module.Flat D B] [Algebra.FormallyUnramified D B] [Algebra.EssFiniteType D B] :
    IsReduced B := by
  let M : Submonoid B := Algebra.algebraMapSubmonoid B (nonZeroDivisors D)

  have hM : M ≤ nonZeroDivisors B := by
    rintro _ ⟨d, hd, rfl⟩
    exact mem_nonZeroDivisors_algebraMap_of_flat D B hd
  have hinj : Function.Injective (algebraMap B (Localization M)) := IsLocalization.injective _ hM

  haveI : Algebra.FormallyUnramified (FractionRing D) (Localization M) :=
    Algebra.FormallyUnramified.of_restrictScalars D _ _
  haveI : Algebra.EssFiniteType (FractionRing D) (Localization M) :=
    Algebra.EssFiniteType.of_comp D _ _
  haveI : IsReduced (Localization M) :=
    Algebra.FormallyUnramified.isReduced_of_field (FractionRing D) (Localization M)
  exact isReduced_of_injective (algebraMap B (Localization M)) hinj

end Algebra
p2m_reactivate "P2MW.S_V3AsmLevel_strict_iso.MvPolynomial P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme.IdealSheafData"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective IsClosedImmersion.of_comp basicOpen_eq_bot_iff Scheme.Hom iSup_affineOpens_eq_top Scheme.Pullback.range_fst LocallyOfFiniteType Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme pullbackSpecIso Spec.map_base Scheme.Hom.comp_base IsReduced.of_openCover Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced IsSeparated HasRingHomProperty.appLE SpecMap_ΓSpecIso_hom isAffineOpen_top Scheme.preimage_basicOpen_top Spec.map_id Etale Scheme.Spec affine_isIntegral_iff FormallyUnramified isReduced_of_isOpenImmersion isReduced_of_isAffine_isReduced HasRingHomProperty Etale.iff_flat_and_formallyUnramified toSpecΓ Scheme.Hom.comp_apply basicOpen_eq_of_affine geometrically range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso"
p2m_open "AlgebraicGeometry"

private theorem isReduced_of_affineOpens (X : Scheme.{u}) (h : ∀ V : X.affineOpens, _root_.IsReduced Γ(X, V)) :
    IsReduced X := by
  haveI : ∀ i, IsReduced ((X.openCoverOfIsOpenCover (fun V : X.affineOpens => (V : X.Opens))
      (iSup_affineOpens_eq_top X)).X i) := fun (V : X.affineOpens) => by
    show IsReduced ((V : X.Opens) : Scheme.{u})
    haveI : _root_.IsReduced Γ((V : X.Opens), ⊤) :=
      isReduced_of_injective (V : X.Opens).topIso.commRingCatIsoToRingEquiv
        (V : X.Opens).topIso.commRingCatIsoToRingEquiv.injective
    exact isReduced_of_isAffine_isReduced _
  exact IsReduced.of_openCover _ (X.openCoverOfIsOpenCover (fun V : X.affineOpens => (V : X.Opens))
    (iSup_affineOpens_eq_top X))

private theorem isReduced_of_flat_of_formallyUnramified {D : Type u} [CommRing D] [IsDomain D] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of D)) [Flat f] [LocallyOfFiniteType f] [FormallyUnramified f] :
    IsReduced X := by
  refine isReduced_of_affineOpens X fun V => ?_
  let φ := (f.appLE ⊤ V le_top).hom
  have hflat : φ.Flat :=
    HasRingHomProperty.appLE (P := @Flat) (f := f) inferInstance ⟨⊤, isAffineOpen_top _⟩ V le_top
  have hft : φ.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) (f := f) inferInstance ⟨⊤, isAffineOpen_top _⟩ V le_top
  have hunr : φ.FormallyUnramified :=
    HasRingHomProperty.appLE (P := @FormallyUnramified) (f := f) inferInstance ⟨⊤, isAffineOpen_top _⟩ V le_top

  haveI : IsDomain Γ(Spec (CommRingCat.of D), ⊤) :=
    MulEquiv.isDomain D (Scheme.ΓSpecIso (CommRingCat.of D)).commRingCatIsoToRingEquiv.toMulEquiv
  letI := φ.toAlgebra
  haveI : Module.Flat Γ(Spec (CommRingCat.of D), ⊤) Γ(X, V) := hflat
  haveI : Algebra.FormallyUnramified Γ(Spec (CommRingCat.of D), ⊤) Γ(X, V) := hunr
  haveI : Algebra.FiniteType Γ(Spec (CommRingCat.of D), ⊤) Γ(X, V) := hft
  exact Algebra.isReduced_of_flat_of_formallyUnramified_of_isDomain Γ(Spec (CommRingCat.of D), ⊤) Γ(X, V)

private theorem isReduced_of_etale {D : Type u} [CommRing D] [IsDomain D] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of D)) [Etale f] : IsReduced X := by
  haveI : Flat f := (Etale.iff_flat_and_formallyUnramified.mp inferInstance).1
  haveI : LocallyOfFiniteType f := inferInstance
  exact isReduced_of_flat_of_formallyUnramified f

end AlgebraicGeometry
p2m_reactivate "P2MW.S_V3AsmLevel_strict_iso.MvPolynomial P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme.IdealSheafData"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective IsClosedImmersion.of_comp basicOpen_eq_bot_iff Scheme.Hom iSup_affineOpens_eq_top Scheme.Pullback.range_fst LocallyOfFiniteType Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme pullbackSpecIso Spec.map_base Scheme.Hom.comp_base IsReduced.of_openCover Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced IsSeparated HasRingHomProperty.appLE SpecMap_ΓSpecIso_hom isAffineOpen_top Scheme.preimage_basicOpen_top Spec.map_id Etale Scheme.Spec affine_isIntegral_iff FormallyUnramified isReduced_of_isOpenImmersion isReduced_of_isAffine_isReduced HasRingHomProperty Etale.iff_flat_and_formallyUnramified toSpecΓ Scheme.Hom.comp_apply basicOpen_eq_of_affine geometrically range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso"
p2m_open "AlgebraicGeometry"

open _root_.AlgebraicGeometry.Polynomial in

private theorem isDomain_polynomial_tensor (k₀ κ : Type u) [Field k₀] [Field κ] [Algebra k₀ κ] :
    IsDomain (TensorProduct k₀ (Polynomial k₀) κ) :=
  MulEquiv.isDomain (Polynomial κ)
    (((Algebra.TensorProduct.comm k₀ (Polynomial k₀) κ).trans (polyEquivTensor k₀ κ).symm).toMulEquiv)

variable {G F : Scheme.{u}} (gF : G ⟶ F) [Etale gF]
  {O k₀ κ : Type u} [CommRing O] [Field k₀] [Field κ] [Algebra k₀ κ]
  (q : O →+* k₀) (hq : Function.Surjective q)
  (fk : F ⟶ Spec (CommRingCat.of k₀))
  (eF : F ≅ Spec (CommRingCat.of (Polynomial k₀)))
  (heF : eF.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ (Polynomial k₀))) = fk)

include hq heF in

private theorem isReduced_pullback_of_etale_over_line
    (fO : G ⟶ Spec (CommRingCat.of O)) (hfO : fO = (gF ≫ fk) ≫ Spec.map (CommRingCat.ofHom q))
    (b : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of O))
    (hb : b = Spec.map (CommRingCat.ofHom (algebraMap k₀ κ)) ≫ Spec.map (CommRingCat.ofHom q)) :
    IsReduced (pullback fO b) := by
  subst hfO hb
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom q)) := IsClosedImmersion.spec_of_surjective _ hq

  haveI := isDomain_polynomial_tensor k₀ κ
  let Fκ := pullback fk (Spec.map (CommRingCat.ofHom (algebraMap k₀ κ)))

  let toA : Fκ ⟶ Spec (CommRingCat.of (TensorProduct k₀ (Polynomial k₀) κ)) :=
    (pullback.congrHom heF.symm rfl).hom ≫
      (pullbackRightPullbackFstIso (Spec.map (CommRingCat.ofHom (algebraMap k₀ (Polynomial k₀))))
        (Spec.map (CommRingCat.ofHom (algebraMap k₀ κ))) eF.hom).inv ≫
      pullback.snd eF.hom _ ≫ (pullbackSpecIso k₀ (Polynomial k₀) κ).hom
  haveI : IsIso toA := by
    dsimp only [toA]
    infer_instance
  haveI : Etale (pullback.snd gF (pullback.fst fk (Spec.map (CommRingCat.ofHom (algebraMap k₀ κ)))) ≫ toA) :=
    inferInstance
  haveI : IsReduced (pullback gF (pullback.fst fk (Spec.map (CommRingCat.ofHom (algebraMap k₀ κ))))) :=
    isReduced_of_etale (pullback.snd gF (pullback.fst fk (Spec.map (CommRingCat.ofHom (algebraMap k₀ κ)))) ≫ toA)

  haveI : IsReduced (pullback (gF ≫ fk) (Spec.map (CommRingCat.ofHom (algebraMap k₀ κ)))) :=
    isReduced_of_isOpenImmersion
      (pullbackRightPullbackFstIso fk (Spec.map (CommRingCat.ofHom (algebraMap k₀ κ))) gF).inv
  exact isReduced_of_isOpenImmersion
    (pullbackCompMonoIso (gF ≫ fk) (Spec.map (CommRingCat.ofHom (algebraMap k₀ κ))) (Spec.map (CommRingCat.ofHom q))).hom

end AlgebraicGeometry
p2m_reactivate "P2MW.S_V3AsmLevel_strict_iso.MvPolynomial P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme.IdealSheafData"

noncomputable section

namespace MvPolynomial
p2m_export "MvPolynomial" "X map R zeroLocus ext support algebraMap_apply ringHom_ext comap vanishingIdeal algebraMap_eq C algHom_ext' algHom_ext map_id CrossingQuotient.Resolution CrossingQuotient.U CrossingQuotient.V CrossingQuotient CrossingQuotient.exists_algEquiv_quotient_span_U_and_span_V_polynomial"
namespace CrossingQuotient
p2m_export "MvPolynomial.CrossingQuotient" "crossingScheme Resolution Resolution.ι Resolution.toCrossing U V U_mul_V lift lift_U lift_V resolutionChart resolutionChart_U resolutionChart_V mk mk_surjective Resolution.isSeparated exists_algEquiv_quotient_span_U_and_span_V_polynomial"
namespace Resolution
p2m_export "MvPolynomial.CrossingQuotient.Resolution" "ι openCover toCrossing ι_toCrossing toSpec ι_toSpec hom_ext isSeparated"
p2m_open "MvPolynomial.CrossingQuotient.Resolution MvPolynomial.CrossingQuotient MvPolynomial"

p2m_open "AlgebraicGeometry P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial AlgebraicGeometry.Polynomial"

universe w

variable {W : Type w} [CommRing W] (t : W)

private def lineVAlgHom : W ⧸ Ideal.span {t} →+* CrossingQuotient W t ⧸ Ideal.span {V t} :=
  Ideal.Quotient.lift (Ideal.span {t}) (algebraMap W _) (fun a ha => by
    rw [Ideal.mem_span_singleton'] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [IsScalarTower.algebraMap_apply W (CrossingQuotient W t) (_ ⧸ _), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact Ideal.mul_mem_left _ _ (algebraMap_mem_span_V' t))

private theorem lineVAlgHom_comp_mk : (lineVAlgHom t).comp (Ideal.Quotient.mk _) = algebraMap W _ :=
  Ideal.Quotient.lift_comp_mk _ _ _

private theorem exists_iso_spec_lineV :
    ∃ eF : Spec (CommRingCat.of (CrossingQuotient W t ⧸ Ideal.span {V t})) ≅
        Spec (CommRingCat.of (Polynomial (W ⧸ Ideal.span {t}))),
      eF.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap (W ⧸ Ideal.span {t}) (Polynomial (W ⧸ Ideal.span {t})))) =
        Spec.map (CommRingCat.ofHom (lineVAlgHom t)) := by
  obtain ⟨-, E, -⟩ := MvPolynomial.CrossingQuotient.exists_algEquiv_quotient_span_U_and_span_V_polynomial t
  refine ⟨⟨Spec.map (CommRingCat.ofHom E.symm.toAlgHom.toRingHom), Spec.map (CommRingCat.ofHom E.toAlgHom.toRingHom), ?_, ?_⟩, ?_⟩
  · rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : E.symm.toAlgHom.toRingHom.comp E.toAlgHom.toRingHom = RingHom.id _ :=
      RingHom.ext fun x => E.symm_apply_apply x
    rw [this, CommRingCat.ofHom_id, Spec.map_id]
  · rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : E.toAlgHom.toRingHom.comp E.symm.toAlgHom.toRingHom = RingHom.id _ :=
      RingHom.ext fun x => E.apply_symm_apply x
    rw [this, CommRingCat.ofHom_id, Spec.map_id]
  · dsimp only
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2

    apply Ideal.Quotient.ringHom_ext
    rw [lineVAlgHom_comp_mk]
    ext a
    change E.symm (algebraMap (W ⧸ Ideal.span {t}) (Polynomial (W ⧸ Ideal.span {t})) (Ideal.Quotient.mk _ a)) =
      algebraMap W _ a
    have ha : algebraMap (W ⧸ Ideal.span {t}) (Polynomial (W ⧸ Ideal.span {t})) (Ideal.Quotient.mk _ a) =
        algebraMap W (Polynomial (W ⧸ Ideal.span {t})) a :=
      (IsScalarTower.algebraMap_apply W (W ⧸ Ideal.span {t}) _ a).symm
    rw [ha]
    exact E.symm.commutes a

private theorem isIntegral_spec_lineV [IsDomain (W ⧸ Ideal.span {t})] :
    IsIntegral (Spec (CommRingCat.of (CrossingQuotient W t ⧸ Ideal.span {V t}))) := by
  obtain ⟨-, E, -⟩ := MvPolynomial.CrossingQuotient.exists_algEquiv_quotient_span_U_and_span_V_polynomial t
  haveI : IsDomain (CrossingQuotient W t ⧸ Ideal.span {V t}) :=
    MulEquiv.isDomain (Polynomial (W ⧸ Ideal.span {t})) E.toMulEquiv
  exact (affine_isIntegral_iff _).mpr ‹_›

section chartPiece

variable (e : ℕ) (he : 0 < e) {Uc : Scheme.{w}} (f : Uc ⟶ crossingScheme (t ^ e)) [Etale f]

private theorem isReduced_chartPiece_strictV [IsDomain (W ⧸ Ideal.span {t})] :
    IsReduced (pullback (pullback.snd f (toCrossing t e)) (strictVι t e he)) := by
  obtain ⟨eF, -⟩ := exists_iso_spec_lineV t
  haveI : IsDomain (Polynomial (W ⧸ Ideal.span {t})) := inferInstance
  haveI : Etale (pullback.snd (pullback.snd f (toCrossing t e)) (strictVι t e he) ≫ eF.hom) := inferInstance
  exact isReduced_of_etale (pullback.snd (pullback.snd f (toCrossing t e)) (strictVι t e he) ≫ eF.hom)

private theorem strictVι_toSpec :
    strictVι t e he ≫ toSpec t e = Spec.map (CommRingCat.ofHom (algebraMap W (CrossingQuotient W t ⧸ Ideal.span {V t}))) := by
  rw [strictVι, Category.assoc, ι_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

variable (hmax : (Ideal.span {t}).IsMaximal) {κ : Type w} [Field κ] (toκ : W →+* κ) (htoκ : toκ t = 0)

include hmax htoκ in

private theorem isReduced_pullback_chartPiece_strictV_fibre :
    IsReduced (pullback (pullback.fst (pullback.snd f (toCrossing t e)) (strictVι t e he) ≫
      (pullback.snd f (toCrossing t e) ≫ toSpec t e)) (Spec.map (CommRingCat.ofHom toκ))) := by
  letI : Field (W ⧸ Ideal.span {t}) := Ideal.Quotient.field (Ideal.span {t})
  have hle : Ideal.span {t} ≤ RingHom.ker toκ := by
    rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]; exact htoκ
  letI : Algebra (W ⧸ Ideal.span {t}) κ := (Ideal.Quotient.lift (Ideal.span {t}) toκ fun a ha => hle ha).toAlgebra
  have halg : (algebraMap (W ⧸ Ideal.span {t}) κ).comp (Ideal.Quotient.mk _) = toκ := Ideal.Quotient.lift_comp_mk _ _ _
  obtain ⟨eF, heF⟩ := exists_iso_spec_lineV t
  refine AlgebraicGeometry.isReduced_pullback_of_etale_over_line
    (pullback.snd (pullback.snd f (toCrossing t e)) (strictVι t e he)) (Ideal.Quotient.mk (Ideal.span {t}))
    Ideal.Quotient.mk_surjective (Spec.map (CommRingCat.ofHom (lineVAlgHom t))) eF heF _ ?_ _ ?_
  ·
    rw [Category.assoc (pullback.snd _ _), ← Spec.map_comp, ← CommRingCat.ofHom_comp, lineVAlgHom_comp_mk,
      ← strictVι_toSpec t e he, ← Category.assoc (pullback.snd _ _) (strictVι t e he), ← pullback.condition,
      Category.assoc]
  · rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, halg]

end chartPiece
p2m_reactivate "P2MW.S_V3AsmLevel_strict_iso.MvPolynomial P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme.IdealSheafData"

private def lineUAlgHom : W ⧸ Ideal.span {t} →+* CrossingQuotient W t ⧸ Ideal.span {U t} :=
  Ideal.Quotient.lift (Ideal.span {t}) (algebraMap W _) (fun a ha => by
    rw [Ideal.mem_span_singleton'] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [IsScalarTower.algebraMap_apply W (CrossingQuotient W t) (_ ⧸ _), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact Ideal.mul_mem_left _ _ (algebraMap_mem_span_U' t))

private theorem lineUAlgHom_comp_mk : (lineUAlgHom t).comp (Ideal.Quotient.mk _) = algebraMap W _ :=
  Ideal.Quotient.lift_comp_mk _ _ _

private theorem exists_iso_spec_lineU :
    ∃ eF : Spec (CommRingCat.of (CrossingQuotient W t ⧸ Ideal.span {U t})) ≅
        Spec (CommRingCat.of (Polynomial (W ⧸ Ideal.span {t}))),
      eF.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap (W ⧸ Ideal.span {t}) (Polynomial (W ⧸ Ideal.span {t})))) =
        Spec.map (CommRingCat.ofHom (lineUAlgHom t)) := by
  obtain ⟨⟨E, -⟩, -⟩ := MvPolynomial.CrossingQuotient.exists_algEquiv_quotient_span_U_and_span_V_polynomial t
  refine ⟨⟨Spec.map (CommRingCat.ofHom E.symm.toAlgHom.toRingHom), Spec.map (CommRingCat.ofHom E.toAlgHom.toRingHom), ?_, ?_⟩, ?_⟩
  · rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : E.symm.toAlgHom.toRingHom.comp E.toAlgHom.toRingHom = RingHom.id _ :=
      RingHom.ext fun x => E.symm_apply_apply x
    rw [this, CommRingCat.ofHom_id, Spec.map_id]
  · rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : E.toAlgHom.toRingHom.comp E.symm.toAlgHom.toRingHom = RingHom.id _ :=
      RingHom.ext fun x => E.apply_symm_apply x
    rw [this, CommRingCat.ofHom_id, Spec.map_id]
  · dsimp only
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2

    apply Ideal.Quotient.ringHom_ext
    rw [lineUAlgHom_comp_mk]
    ext a
    change E.symm (algebraMap (W ⧸ Ideal.span {t}) (Polynomial (W ⧸ Ideal.span {t})) (Ideal.Quotient.mk _ a)) =
      algebraMap W _ a
    have ha : algebraMap (W ⧸ Ideal.span {t}) (Polynomial (W ⧸ Ideal.span {t})) (Ideal.Quotient.mk _ a) =
        algebraMap W (Polynomial (W ⧸ Ideal.span {t})) a :=
      (IsScalarTower.algebraMap_apply W (W ⧸ Ideal.span {t}) _ a).symm
    rw [ha]
    exact E.symm.commutes a

private theorem isIntegral_spec_lineU [IsDomain (W ⧸ Ideal.span {t})] :
    IsIntegral (Spec (CommRingCat.of (CrossingQuotient W t ⧸ Ideal.span {U t}))) := by
  obtain ⟨⟨E, -⟩, -⟩ := MvPolynomial.CrossingQuotient.exists_algEquiv_quotient_span_U_and_span_V_polynomial t
  haveI : IsDomain (CrossingQuotient W t ⧸ Ideal.span {U t}) :=
    MulEquiv.isDomain (Polynomial (W ⧸ Ideal.span {t})) E.toMulEquiv
  exact (affine_isIntegral_iff _).mpr ‹_›

section chartPieceU

variable (e : ℕ) (he : 0 < e) {Uc : Scheme.{w}} (f : Uc ⟶ crossingScheme (t ^ e)) [Etale f]

private theorem isReduced_chartPiece_strictU [IsDomain (W ⧸ Ideal.span {t})] :
    IsReduced (pullback (pullback.snd f (toCrossing t e)) (strictUι t e he)) := by
  obtain ⟨eF, -⟩ := exists_iso_spec_lineU t
  haveI : IsDomain (Polynomial (W ⧸ Ideal.span {t})) := inferInstance
  haveI : Etale (pullback.snd (pullback.snd f (toCrossing t e)) (strictUι t e he) ≫ eF.hom) := inferInstance
  exact isReduced_of_etale (pullback.snd (pullback.snd f (toCrossing t e)) (strictUι t e he) ≫ eF.hom)

private theorem strictUι_toSpec :
    strictUι t e he ≫ toSpec t e = Spec.map (CommRingCat.ofHom (algebraMap W (CrossingQuotient W t ⧸ Ideal.span {U t}))) := by
  rw [strictUι, Category.assoc, ι_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

variable (hmax : (Ideal.span {t}).IsMaximal) {κ : Type w} [Field κ] (toκ : W →+* κ) (htoκ : toκ t = 0)

include hmax htoκ in

private theorem isReduced_pullback_chartPiece_strictU_fibre :
    IsReduced (pullback (pullback.fst (pullback.snd f (toCrossing t e)) (strictUι t e he) ≫
      (pullback.snd f (toCrossing t e) ≫ toSpec t e)) (Spec.map (CommRingCat.ofHom toκ))) := by
  letI : Field (W ⧸ Ideal.span {t}) := Ideal.Quotient.field (Ideal.span {t})
  have hle : Ideal.span {t} ≤ RingHom.ker toκ := by
    rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]; exact htoκ
  letI : Algebra (W ⧸ Ideal.span {t}) κ := (Ideal.Quotient.lift (Ideal.span {t}) toκ fun a ha => hle ha).toAlgebra
  have halg : (algebraMap (W ⧸ Ideal.span {t}) κ).comp (Ideal.Quotient.mk _) = toκ := Ideal.Quotient.lift_comp_mk _ _ _
  obtain ⟨eF, heF⟩ := exists_iso_spec_lineU t
  refine AlgebraicGeometry.isReduced_pullback_of_etale_over_line
    (pullback.snd (pullback.snd f (toCrossing t e)) (strictUι t e he)) (Ideal.Quotient.mk (Ideal.span {t}))
    Ideal.Quotient.mk_surjective (Spec.map (CommRingCat.ofHom (lineUAlgHom t))) eF heF _ ?_ _ ?_
  ·
    rw [Category.assoc (pullback.snd _ _), ← Spec.map_comp, ← CommRingCat.ofHom_comp, lineUAlgHom_comp_mk,
      ← strictUι_toSpec t e he, ← Category.assoc (pullback.snd _ _) (strictUι t e he), ← pullback.condition,
      Category.assoc]
  · rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, halg]

end chartPieceU
p2m_reactivate "P2MW.S_V3AsmLevel_strict_iso.MvPolynomial P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme.IdealSheafData"

end MvPolynomial.CrossingQuotient.Resolution
p2m_reactivate "P2MW.S_V3AsmLevel_strict_iso.MvPolynomial P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme.IdealSheafData"
p2m_reactivate "P2MW.S_V3AsmLevel_strict_iso.MvPolynomial P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme.IdealSheafData"
p2m_reactivate "P2MW.S_V3AsmLevel_strict_iso.MvPolynomial P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme.IdealSheafData"

end
p2m_reactivate "P2MW.S_V3AsmLevel_strict_iso.MvPolynomial P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme.IdealSheafData"

namespace V3Glue
p2m_export "V3Glue" "LevelSite.Node ChartInput.ηG_inl ChartInput.coe_support_compG ChartInput ChartInput.exists_iso_geometricFibre_strictTransform"
namespace LevelSite
p2m_export "V3Glue.LevelSite" "Node xpt HasOrientedCrossingCharts ModelHyps EtNbhd chartData rawChartInputOfDR chartInputOfDR"
p2m_open "V3Glue.LevelSite V3Glue"

p2m_open "ModularCurve MvPolynomial P2MW.S_V3AsmLevel_strict_iso.MvPolynomial"

section Orient

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔛 : DRModelPackageLevel N₀ q hqN)
  (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O)
  (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (τ : DRLevel.R q →+* κ)
  (bc : DRLevel.fibre (N₀ := N₀) τ ⟶ DRLevel.XO (N₀ := N₀) ρO)
  [Finite (Node 𝔛 κ τ)]
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)}) (M : ModelHyps q O)
  (hC : HasOrientedCrossingCharts 𝔛 O ρO κ τ bc) (ET : EtNbhd)
  (hxinj : Function.Injective (fun n : Node 𝔛 κ τ => xpt 𝔛 bc n))
  (hxcl : ∀ n : Node 𝔛 κ τ, IsClosed ({xpt 𝔛 bc n} : Set (DRLevel.XO (N₀ := N₀) ρO)))

private noncomputable def toChartU (n : Node 𝔛 κ τ) (y : (chartInputOfDR 𝔛 O ρO κ τ bc hϖ M hC ET hxinj hxcl).U n) : (chartData 𝔛 O ρO κ τ bc hC n).U :=
  ((DRLevel.XO (N₀ := N₀) ρO).homOfLE ((rawChartInputOfDR 𝔛 O ρO κ τ bc hϖ M hC hxinj hxcl).U_le
    ((rawChartInputOfDR 𝔛 O ρO κ τ bc hϖ M hC hxinj hxcl).hnbhd_of ET) n)).base y

private theorem coe_toChartU (n : Node 𝔛 κ τ) (y : (chartInputOfDR 𝔛 O ρO κ τ bc hϖ M hC ET hxinj hxcl).U n) :
    ((toChartU 𝔛 O ρO κ τ bc hϖ M hC ET hxinj hxcl n y : (chartData 𝔛 O ρO κ τ bc hC n).U) : DRLevel.XO (N₀ := N₀) ρO) = (y : DRLevel.XO (N₀ := N₀) ρO) := by
  unfold toChartU
  have h3 := congr($((DRLevel.XO (N₀ := N₀) ρO).homOfLE_ι ((rawChartInputOfDR 𝔛 O ρO κ τ bc hϖ M hC hxinj hxcl).U_le
        ((rawChartInputOfDR 𝔛 O ρO κ τ bc hϖ M hC hxinj hxcl).hnbhd_of ET) n)).base y)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h3
  exact h3

private theorem ι_toChartU (n : Node 𝔛 κ τ) (y : (chartInputOfDR 𝔛 O ρO κ τ bc hϖ M hC ET hxinj hxcl).U n) :
    ((chartData 𝔛 O ρO κ τ bc hC n).U).ι.base (toChartU 𝔛 O ρO κ τ bc hϖ M hC ET hxinj hxcl n y) = (y : DRLevel.XO (N₀ := N₀) ρO) :=
  coe_toChartU 𝔛 O ρO κ τ bc hϖ M hC ET hxinj hxcl n y

private theorem chartInputOfDR_f_base (n : Node 𝔛 κ τ) (y : (chartInputOfDR 𝔛 O ρO κ τ bc hϖ M hC ET hxinj hxcl).U n) :
    ((chartInputOfDR 𝔛 O ρO κ τ bc hϖ M hC ET hxinj hxcl).f n).base y =
      (chartData 𝔛 O ρO κ τ bc hC n).f.base (toChartU 𝔛 O ρO κ τ bc hϖ M hC ET hxinj hxcl n y) := rfl

private theorem _root_.V3Glue.LevelSite.orient_inf (n : Node 𝔛 κ τ) (y : (chartInputOfDR 𝔛 O ρO κ τ bc hϖ M hC ET hxinj hxcl).U n)
    (h : CrossingQuotient.V (((q : ℕ) : O) ^ (chartData 𝔛 O ρO κ τ bc hC n).e) ∈
      (((chartInputOfDR 𝔛 O ρO κ τ bc hϖ M hC ET hxinj hxcl).f n).base y).asIdeal) :
    (y : DRLevel.XO (N₀ := N₀) ρO) ∈ Set.range (𝔛.comp κ τ 0 ≫ bc).base := by
  rw [← coe_toChartU 𝔛 O ρO κ τ bc hϖ M hC ET hxinj hxcl n y]
  first
    | exact (chartData 𝔛 O ρO κ τ bc hC n).orient_inf _ h
    | simpa using (chartData 𝔛 O ρO κ τ bc hC n).orient_inf _ h
    | (have h' := (chartData 𝔛 O ρO κ τ bc hC n).orient_inf _ h; simp at h' ⊢; exact h')

p2m_export "V3Glue.LevelSite" "orient_inf"
private theorem _root_.V3Glue.LevelSite.orient_zero (n : Node 𝔛 κ τ) (y : (chartInputOfDR 𝔛 O ρO κ τ bc hϖ M hC ET hxinj hxcl).U n)
    (h : CrossingQuotient.U (((q : ℕ) : O) ^ (chartData 𝔛 O ρO κ τ bc hC n).e) ∈
      (((chartInputOfDR 𝔛 O ρO κ τ bc hϖ M hC ET hxinj hxcl).f n).base y).asIdeal) :
    (y : DRLevel.XO (N₀ := N₀) ρO) ∈ Set.range (𝔛.comp κ τ 1 ≫ bc).base := by
  rw [← coe_toChartU 𝔛 O ρO κ τ bc hϖ M hC ET hxinj hxcl n y]
  first
    | exact (chartData 𝔛 O ρO κ τ bc hC n).orient_zero _ h
    | simpa using (chartData 𝔛 O ρO κ τ bc hC n).orient_zero _ h
    | (have h' := (chartData 𝔛 O ρO κ τ bc hC n).orient_zero _ h; simp at h' ⊢; exact h')

p2m_export "V3Glue.LevelSite" "orient_zero"
private theorem _root_.V3Glue.LevelSite.orient_inf_conv (n : Node 𝔛 κ τ) (y : (chartInputOfDR 𝔛 O ρO κ τ bc hϖ M hC ET hxinj hxcl).U n)
    (h : (y : DRLevel.XO (N₀ := N₀) ρO) ∈ Set.range (𝔛.comp κ τ 0 ≫ bc).base) :
    CrossingQuotient.V (((q : ℕ) : O) ^ (chartData 𝔛 O ρO κ τ bc hC n).e) ∈
      (((chartInputOfDR 𝔛 O ρO κ τ bc hϖ M hC ET hxinj hxcl).f n).base y).asIdeal := by
  refine (chartData 𝔛 O ρO κ τ bc hC n).orient_inf_conv (toChartU 𝔛 O ρO κ τ bc hϖ M hC ET hxinj hxcl n y) ?_
  rw [ι_toChartU]; exact h

p2m_export "V3Glue.LevelSite" "orient_inf_conv"
private theorem _root_.V3Glue.LevelSite.orient_zero_conv (n : Node 𝔛 κ τ) (y : (chartInputOfDR 𝔛 O ρO κ τ bc hϖ M hC ET hxinj hxcl).U n)
    (h : (y : DRLevel.XO (N₀ := N₀) ρO) ∈ Set.range (𝔛.comp κ τ 1 ≫ bc).base) :
    CrossingQuotient.U (((q : ℕ) : O) ^ (chartData 𝔛 O ρO κ τ bc hC n).e) ∈
      (((chartInputOfDR 𝔛 O ρO κ τ bc hϖ M hC ET hxinj hxcl).f n).base y).asIdeal := by
  refine (chartData 𝔛 O ρO κ τ bc hC n).orient_zero_conv (toChartU 𝔛 O ρO κ τ bc hϖ M hC ET hxinj hxcl n y) ?_
  rw [ι_toChartU]; exact h

p2m_export "V3Glue.LevelSite" "orient_zero_conv"
end Orient
p2m_reactivate "P2MW.S_V3AsmLevel_strict_iso.MvPolynomial P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme.IdealSheafData"

end V3Glue.LevelSite
p2m_reactivate "P2MW.S_V3AsmLevel_strict_iso.MvPolynomial P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme.IdealSheafData"
p2m_reactivate "P2MW.S_V3AsmLevel_strict_iso.MvPolynomial P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme.IdealSheafData"

noncomputable section

namespace V3AsmLevel
p2m_export "V3AsmLevel" "πX bc bc_fst bc_snd SiteHyps R C D Y toDR toBase hq hRF ξ gRes hgRes comp"
p2m_open "V3AsmLevel"

p2m_open "ModularCurve MvPolynomial P2MW.S_V3AsmLevel_strict_iso.MvPolynomial MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient"

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔛 : DRModelPackageLevel N₀ q hqN) (O : Type) [CommRing O]
  [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O)
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
  (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
  (H : SiteHyps 𝔛 O ρO κ toκ) (hξ : ∀ j, ξ 𝔛 O ρO κ toκ j ∈ (C 𝔛 O ρO κ toκ hϖ H).X0)

include 𝔛 O ρO hϖ κ toκ H hξ

private theorem etale_f (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) : Etale ((C 𝔛 O ρO κ toκ hϖ H).f n) := by
  haveI := H.nodeFinite
  exact (R 𝔛 O ρO κ toκ hϖ H).etale_toChartInput_f ((R 𝔛 O ρO κ toκ hϖ H).hnbhd_of H.ET) n

private theorem isPullback_bc :
    IsPullback (bc (N₀ := N₀) O ρO κ toκ) (pullback.snd _ _) (πX (N₀ := N₀) O ρO) (Spec.map (CommRingCat.ofHom toκ)) := by
  have hρι : Spec.map (CommRingCat.ofHom toκ) ≫ Spec.map (CommRingCat.ofHom ρO) =
      Spec.map (CommRingCat.ofHom (toκ.comp ρO)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have key : IsPullback (bc (N₀ := N₀) O ρO κ toκ ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))
      (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO)))) (DRLevel.toBase N₀ q)
      (Spec.map (CommRingCat.ofHom toκ) ≫ Spec.map (CommRingCat.ofHom ρO)) := by
    rw [bc_fst, hρι]
    exact IsPullback.of_hasPullback _ _
  exact IsPullback.of_right key (bc_snd (N₀ := N₀) O ρO κ toκ) (IsPullback.of_hasPullback _ _)

private theorem ker_toκ : RingHom.ker toκ = IsLocalRing.maximalIdeal O := by
  refine ((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (RingHom.ker_ne_top toκ) ?_).symm
  rw [hϖ, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]

private theorem range_bc : Set.range (bc (N₀ := N₀) O ρO κ toκ).base = (πX (N₀ := N₀) O ρO).base ⁻¹' {IsLocalRing.closedPoint O} := by
  rw [AlgebraicGeometry.IsPullback.range_fst' (isPullback_bc 𝔛 O ρO hϖ κ toκ H hξ),
    AlgebraicGeometry.range_specMap_of_ker_eq_maximalIdeal toκ (ker_toκ 𝔛 O ρO hϖ κ toκ H hξ)]

private theorem πX_bc_apply (w : ↥(DRLevel.fibre (N₀ := N₀) (toκ.comp ρO))) :
    (πX (N₀ := N₀) O ρO).base ((bc (N₀ := N₀) O ρO κ toκ).base w) = IsLocalRing.closedPoint O := by
  have hw : (bc (N₀ := N₀) O ρO κ toκ).base w ∈ Set.range (bc (N₀ := N₀) O ρO κ toκ).base := ⟨w, rfl⟩
  rw [range_bc 𝔛 O ρO hϖ κ toκ H hξ] at hw
  exact hw

private abbrev iB : Spec (CommRingCat.of (O ⧸ IsLocalRing.maximalIdeal O)) ⟶ Spec (CommRingCat.of O) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)))

private theorem iB_isClosedImmersion : IsClosedImmersion (iB O) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

private theorem iB_mono : Mono (iB O) := by
  haveI : Epi (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O))) :=
    ConcreteCategory.epi_of_surjective _ Ideal.Quotient.mk_surjective
  show Mono (Scheme.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O))).op)
  infer_instance

private def resκ : O ⧸ IsLocalRing.maximalIdeal O →+* κ :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) toκ (fun a ha => by
    rwa [← ker_toκ 𝔛 O ρO hϖ κ toκ H hξ, RingHom.mem_ker] at ha)

private theorem resκ_comp_mk : (resκ 𝔛 O ρO hϖ κ toκ H hξ).comp (Ideal.Quotient.mk _) = toκ := Ideal.Quotient.lift_comp_mk _ _ _

private abbrev aB : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of (O ⧸ IsLocalRing.maximalIdeal O)) :=
  Spec.map (CommRingCat.ofHom (resκ 𝔛 O ρO hϖ κ toκ H hξ))

private theorem aB_flat : Flat (aB 𝔛 O ρO hϖ κ toκ H hξ) := by
  letI : Field (O ⧸ IsLocalRing.maximalIdeal O) := Ideal.Quotient.field _
  letI := (resκ 𝔛 O ρO hϖ κ toκ H hξ).toAlgebra
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap (O ⧸ IsLocalRing.maximalIdeal O) κ)))
  infer_instance

private theorem specMap_toκ_eq : Spec.map (CommRingCat.ofHom toκ) = aB 𝔛 O ρO hϖ κ toκ H hξ ≫ iB O := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, resκ_comp_mk]

private theorem isDomain_quot_p : IsDomain (O ⧸ Ideal.span {((q : ℕ) : O)}) := by
  rw [← hϖ]; infer_instance

private abbrev lamInf (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) :
    Spec (CommRingCat.of (CrossingQuotient O ((q : ℕ) : O) ⧸ Ideal.span {CrossingQuotient.V ((q : ℕ) : O)})) ⟶
      (C 𝔛 O ρO κ toκ hϖ H).Res n :=
  MvPolynomial.CrossingQuotient.Resolution.strictVι ((q : ℕ) : O) ((C 𝔛 O ρO κ toκ hϖ H).thick n)
    ((C 𝔛 O ρO κ toκ hϖ H).one_le_thick n)

private abbrev lamZero (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) :
    Spec (CommRingCat.of (CrossingQuotient O ((q : ℕ) : O) ⧸ Ideal.span {CrossingQuotient.U ((q : ℕ) : O)})) ⟶
      (C 𝔛 O ρO κ toκ hϖ H).Res n :=
  MvPolynomial.CrossingQuotient.Resolution.strictUι ((q : ℕ) : O) ((C 𝔛 O ρO κ toκ hϖ H).thick n)
    ((C 𝔛 O ρO κ toκ hϖ H).one_le_thick n)

private theorem lamInf_isClosedImmersion (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) : IsClosedImmersion (lamInf 𝔛 O ρO hϖ κ toκ H n) :=
  MvPolynomial.CrossingQuotient.Resolution.isClosedImmersion_strictVι _ _ _
private theorem lamZero_isClosedImmersion (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) : IsClosedImmersion (lamZero 𝔛 O ρO hϖ κ toκ H n) :=
  MvPolynomial.CrossingQuotient.Resolution.isClosedImmersion_strictUι _ _ _
private theorem lamInf_ρ_isClosedImmersion (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) : IsClosedImmersion (lamInf 𝔛 O ρO hϖ κ toκ H n ≫ (C 𝔛 O ρO κ toκ hϖ H).ρ n) :=
  MvPolynomial.CrossingQuotient.Resolution.isClosedImmersion_strictVι_toCrossing _ _ _
private theorem lamZero_ρ_isClosedImmersion (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) : IsClosedImmersion (lamZero 𝔛 O ρO hϖ κ toκ H n ≫ (C 𝔛 O ρO κ toκ hϖ H).ρ n) :=
  MvPolynomial.CrossingQuotient.Resolution.isClosedImmersion_strictUι_toCrossing _ _ _

private theorem isReduced_pieceInf (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) :
    IsReduced (pullback ((C 𝔛 O ρO κ toκ hϖ H).g n) (lamInf 𝔛 O ρO hϖ κ toκ H n)) := by
  exact @MvPolynomial.CrossingQuotient.Resolution.isReduced_chartPiece_strictV O _ ((q : ℕ) : O)
    ((C 𝔛 O ρO κ toκ hϖ H).thick n) ((C 𝔛 O ρO κ toκ hϖ H).one_le_thick n) _
    ((C 𝔛 O ρO κ toκ hϖ H).f n) (etale_f 𝔛 O ρO hϖ κ toκ H hξ n) (isDomain_quot_p 𝔛 O ρO hϖ κ toκ H hξ)

private theorem isReduced_pieceZero (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) :
    IsReduced (pullback ((C 𝔛 O ρO κ toκ hϖ H).g n) (lamZero 𝔛 O ρO hϖ κ toκ H n)) := by
  exact @MvPolynomial.CrossingQuotient.Resolution.isReduced_chartPiece_strictU O _ ((q : ℕ) : O)
    ((C 𝔛 O ρO κ toκ hϖ H).thick n) ((C 𝔛 O ρO κ toκ hϖ H).one_le_thick n) _
    ((C 𝔛 O ρO κ toκ hϖ H).f n) (etale_f 𝔛 O ρO hϖ κ toκ H hξ n) (isDomain_quot_p 𝔛 O ρO hϖ κ toκ H hξ)

private theorem hGκ_inf (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) :
    IsReduced (pullback (pullback.fst ((C 𝔛 O ρO κ toκ hϖ H).g n) (lamInf 𝔛 O ρO hϖ κ toκ H n) ≫
      (C 𝔛 O ρO κ toκ hϖ H).toB n) (Spec.map (CommRingCat.ofHom toκ))) := by
  exact @MvPolynomial.CrossingQuotient.Resolution.isReduced_pullback_chartPiece_strictV_fibre O _ ((q : ℕ) : O)
    ((C 𝔛 O ρO κ toκ hϖ H).thick n) ((C 𝔛 O ρO κ toκ hϖ H).one_le_thick n) _
    ((C 𝔛 O ρO κ toκ hϖ H).f n) (etale_f 𝔛 O ρO hϖ κ toκ H hξ n)
    (hϖ ▸ IsLocalRing.maximalIdeal.isMaximal O) κ _ toκ (by rw [map_natCast, CharP.cast_eq_zero])

private theorem hGκ_zero (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) :
    IsReduced (pullback (pullback.fst ((C 𝔛 O ρO κ toκ hϖ H).g n) (lamZero 𝔛 O ρO hϖ κ toκ H n) ≫
      (C 𝔛 O ρO κ toκ hϖ H).toB n) (Spec.map (CommRingCat.ofHom toκ))) := by
  exact @MvPolynomial.CrossingQuotient.Resolution.isReduced_pullback_chartPiece_strictU_fibre O _ ((q : ℕ) : O)
    ((C 𝔛 O ρO κ toκ hϖ H).thick n) ((C 𝔛 O ρO κ toκ hϖ H).one_le_thick n) _
    ((C 𝔛 O ρO κ toκ hϖ H).f n) (etale_f 𝔛 O ρO hϖ κ toκ H hξ n)
    (hϖ ▸ IsLocalRing.maximalIdeal.isMaximal O) κ _ toκ (by rw [map_natCast, CharP.cast_eq_zero])

private theorem horientInf_fwd (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (y : (C 𝔛 O ρO κ toκ hϖ H).U n)
    (h : ((C 𝔛 O ρO κ toκ hϖ H).f n).base y ∈
      Set.range (lamInf 𝔛 O ρO hϖ κ toκ H n ≫ (C 𝔛 O ρO κ toκ hϖ H).ρ n).base) :
    (y : DRLevel.XO (N₀ := N₀) ρO) ∈ Set.range (𝔛.comp κ (toκ.comp ρO) 0 ≫ bc (N₀ := N₀) O ρO κ toκ).base := by
  haveI := H.nodeFinite
  exact V3Glue.LevelSite.orient_inf 𝔛 O ρO κ (toκ.comp ρO) (bc (N₀ := N₀) O ρO κ toκ) hϖ H.model H.hC H.ET H.hxinj H.hxcl n y
    ((MvPolynomial.CrossingQuotient.Resolution.mem_range_strictVι_toCrossing_iff _ _ _ _).mp h)

private theorem horientInf_conv (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (y : (C 𝔛 O ρO κ toκ hϖ H).U n)
    (h : (y : DRLevel.XO (N₀ := N₀) ρO) ∈ Set.range (𝔛.comp κ (toκ.comp ρO) 0 ≫ bc (N₀ := N₀) O ρO κ toκ).base) :
    ((C 𝔛 O ρO κ toκ hϖ H).f n).base y ∈
      Set.range (lamInf 𝔛 O ρO hϖ κ toκ H n ≫ (C 𝔛 O ρO κ toκ hϖ H).ρ n).base := by
  haveI := H.nodeFinite
  exact (MvPolynomial.CrossingQuotient.Resolution.mem_range_strictVι_toCrossing_iff _ _ _ _).mpr
    (V3Glue.LevelSite.orient_inf_conv 𝔛 O ρO κ (toκ.comp ρO) (bc (N₀ := N₀) O ρO κ toκ) hϖ H.model H.hC H.ET H.hxinj H.hxcl n y h)

private theorem horientZero_fwd (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (y : (C 𝔛 O ρO κ toκ hϖ H).U n)
    (h : ((C 𝔛 O ρO κ toκ hϖ H).f n).base y ∈
      Set.range (lamZero 𝔛 O ρO hϖ κ toκ H n ≫ (C 𝔛 O ρO κ toκ hϖ H).ρ n).base) :
    (y : DRLevel.XO (N₀ := N₀) ρO) ∈ Set.range (𝔛.comp κ (toκ.comp ρO) 1 ≫ bc (N₀ := N₀) O ρO κ toκ).base := by
  haveI := H.nodeFinite
  exact V3Glue.LevelSite.orient_zero 𝔛 O ρO κ (toκ.comp ρO) (bc (N₀ := N₀) O ρO κ toκ) hϖ H.model H.hC H.ET H.hxinj H.hxcl n y
    ((MvPolynomial.CrossingQuotient.Resolution.mem_range_strictUι_toCrossing_iff _ _ _ _).mp h)

private theorem horientZero_conv (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (y : (C 𝔛 O ρO κ toκ hϖ H).U n)
    (h : (y : DRLevel.XO (N₀ := N₀) ρO) ∈ Set.range (𝔛.comp κ (toκ.comp ρO) 1 ≫ bc (N₀ := N₀) O ρO κ toκ).base) :
    ((C 𝔛 O ρO κ toκ hϖ H).f n).base y ∈
      Set.range (lamZero 𝔛 O ρO hϖ κ toκ H n ≫ (C 𝔛 O ρO κ toκ hϖ H).ρ n).base := by
  haveI := H.nodeFinite
  exact (MvPolynomial.CrossingQuotient.Resolution.mem_range_strictUι_toCrossing_iff _ _ _ _).mpr
    (V3Glue.LevelSite.orient_zero_conv 𝔛 O ρO κ (toκ.comp ρO) (bc (N₀ := N₀) O ρO κ toκ) hϖ H.model H.hC H.ET H.hxinj H.hxcl n y h)

private theorem x_mem_range_comp0 (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) :
    (C 𝔛 O ρO κ toκ hϖ H).x n ∈ Set.range (𝔛.comp κ (toκ.comp ρO) 0 ≫ bc (N₀ := N₀) O ρO κ toκ).base :=
  ⟨(pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n, rfl⟩

private theorem x_mem_range_comp1 (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) :
    (C 𝔛 O ρO κ toκ hϖ H).x n ∈ Set.range (𝔛.comp κ (toκ.comp ρO) 1 ≫ bc (N₀ := N₀) O ρO κ toκ).base :=
  ⟨(pullback.snd (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n, by
    rw [← Scheme.Hom.comp_apply, ← pullback.condition_assoc]; rfl⟩

private theorem nonempty_node : Nonempty (V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) := by
  obtain ⟨P, hP⟩ := ModularCurve.ssPlaces_nonempty q N₀ hqN κ
  exact ⟨(𝔛.nodeEquiv κ (toκ.comp ρO)).symm ⟨P, hP⟩⟩

private theorem exists_factor_comp_inl (j : Fin 2) :
    ∃ s₀ : (comp 𝔛 O ρO κ toκ hϖ H hξ (Sum.inl j)).subscheme ⟶ Spec (CommRingCat.of (O ⧸ IsLocalRing.maximalIdeal O)),
      (comp 𝔛 O ρO κ toκ hϖ H hξ (Sum.inl j)).subschemeι ≫ toDR 𝔛 O ρO κ toκ hϖ H ≫ πX (N₀ := N₀) O ρO = s₀ ≫ iB O := by
  unfold toDR D

  have hS : Set.range (comp 𝔛 O ρO κ toκ hϖ H hξ (Sum.inl j)).subschemeι.base =
      closure {(C 𝔛 O ρO κ toκ hϖ H).toGlueInput.ιX0.base ⟨ξ 𝔛 O ρO κ toκ j, hξ j⟩} := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    unfold comp
    erw [V3Glue.ChartInput.coe_support_compG, V3Glue.ChartInput.ηG_inl]
  have hy : (toDR 𝔛 O ρO κ toκ hϖ H ≫ πX (N₀ := N₀) O ρO).base
      ((C 𝔛 O ρO κ toκ hϖ H).toGlueInput.ιX0.base ⟨ξ 𝔛 O ρO κ toκ j, hξ j⟩) = IsLocalRing.closedPoint O := by
    have h1 := congr($((C 𝔛 O ρO κ toκ hϖ H).toGlueInput.ιX0_toDR).base ⟨ξ 𝔛 O ρO κ toκ j, hξ j⟩)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h1 ⊢
    erw [h1]

    refine Fin.cases ?_ (fun i => ?_) j <;> exact πX_bc_apply 𝔛 O ρO hϖ κ toκ H hξ _
  have hall := AlgebraicGeometry.forall_comp_eq_of_range_eq_closure _ (toDR 𝔛 O ρO κ toκ hϖ H ≫ πX (N₀ := N₀) O ρO) hS hy
    (IsLocalRing.isClosed_singleton_closedPoint O)
  haveI : IsReduced (comp 𝔛 O ρO κ toκ hϖ H hξ (Sum.inl j)).subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  obtain ⟨s₀, hs₀⟩ := AlgebraicGeometry.exists_lift_specQuotient
    ((comp 𝔛 O ρO κ toκ hϖ H hξ (Sum.inl j)).subschemeι ≫ toDR 𝔛 O ρO κ toκ hϖ H ≫ πX (N₀ := N₀) O ρO)
    (IsLocalRing.maximalIdeal O)
    (fun r hr => AlgebraicGeometry.preimage_basicOpen_eq_bot_of_forall_eq_closedPoint _ hall r hr)
  exact ⟨s₀, hs₀.symm⟩

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

private theorem strict_iso_inf : ∃ e : pullback ((comp 𝔛 O ρO κ toκ hϖ H hξ (Sum.inl 0)).subschemeι ≫ toBase 𝔛 O ρO κ toκ hϖ H)
      (Spec.map (CommRingCat.ofHom toκ)) ⟶ DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO),
    IsIso e ∧ e ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      e ≫ 𝔛.comp κ (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ =
        pullback.fst _ _ ≫ (comp 𝔛 O ρO κ toκ hϖ H hξ (Sum.inl 0)).subschemeι ≫ toDR 𝔛 O ρO κ toκ hϖ H := by
  unfold toBase toDR D comp
  obtain ⟨n₀⟩ := nonempty_node 𝔛 O ρO hϖ κ toκ H hξ
  haveI : ∀ n, IsReduced (pullback ((C 𝔛 O ρO κ toκ hϖ H).g n) (lamInf 𝔛 O ρO hϖ κ toκ H n)) :=
    fun n => isReduced_pieceInf 𝔛 O ρO hϖ κ toκ H hξ n
  haveI : @Mono Scheme _ _ (C 𝔛 O ρO κ toκ hϖ H).B (iB O) := iB_mono 𝔛 O ρO hϖ κ toκ H hξ
  haveI : Flat (aB 𝔛 O ρO hϖ κ toκ H hξ) := aB_flat 𝔛 O ρO hϖ κ toκ H hξ
  haveI : ∀ n, IsClosedImmersion (lamInf 𝔛 O ρO hϖ κ toκ H n) := fun n => lamInf_isClosedImmersion 𝔛 O ρO hϖ κ toκ H hξ n
  haveI : ∀ n, IsClosedImmersion (lamInf 𝔛 O ρO hϖ κ toκ H n ≫ (C 𝔛 O ρO κ toκ hϖ H).ρ n) :=
    fun n => lamInf_ρ_isClosedImmersion 𝔛 O ρO hϖ κ toκ H hξ n
  obtain ⟨s₀, hs₀⟩ := exists_factor_comp_inl 𝔛 O ρO hϖ κ toκ H hξ 0
  haveI := 𝔛.comp_isClosedImmersion κ (toκ.comp ρO) 0
  haveI := 𝔛.isIntegral_fibre0 (toκ.comp ρO)
  obtain ⟨e, he₁, he₂, he₃⟩ := (C 𝔛 O ρO κ toκ hϖ H).exists_iso_geometricFibre_strictTransform
    (hRF 𝔛 O ρO κ toκ hϖ H) (gRes 𝔛 O ρO κ toκ hϖ H) (hgRes 𝔛 O ρO κ toκ hϖ H)
    (ξ 𝔛 O ρO κ toκ) hξ 0
    (𝔛.comp κ (toκ.comp ρO) 0) (bc (N₀ := N₀) O ρO κ toκ) (pullback.snd _ _) (Spec.map (CommRingCat.ofHom toκ))
    (isPullback_bc 𝔛 O ρO hϖ κ toκ H hξ)
    rfl
    (DRModelPackageLevel.preimage_closure_image_range_comp_eq_of_comp_fst_eq N₀ q hqN 𝔛 O ρO κ toκ (bc (N₀ := N₀) O ρO κ toκ)
      (bc_fst (N₀ := N₀) O ρO κ toκ) 0)
    (IsLocalRing.isClosed_singleton_closedPoint O) (range_bc 𝔛 O ρO hϖ κ toκ H hξ)
    (fun r => πX_bc_apply 𝔛 O ρO hϖ κ toκ H hξ _)
    (lamInf 𝔛 O ρO hϖ κ toκ H) (horientInf_fwd 𝔛 O ρO hϖ κ toκ H hξ) (horientInf_conv 𝔛 O ρO hϖ κ toκ H hξ)
    (x_mem_range_comp0 𝔛 O ρO hϖ κ toκ H hξ)
    n₀ (iB O) (aB 𝔛 O ρO hϖ κ toκ H hξ) (specMap_toκ_eq 𝔛 O ρO hϖ κ toκ H hξ) s₀ hs₀ (hGκ_inf 𝔛 O ρO hϖ κ toκ H hξ n₀)
  refine ⟨e, he₁, ?_, he₃⟩
  rw [← 𝔛.comp_over κ (toκ.comp ρO) 0]
  exact he₂

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

private theorem strict_iso_zero : ∃ e : pullback ((comp 𝔛 O ρO κ toκ hϖ H hξ (Sum.inl 1)).subschemeι ≫ toBase 𝔛 O ρO κ toκ hϖ H)
      (Spec.map (CommRingCat.ofHom toκ)) ⟶ DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO),
    IsIso e ∧ e ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      e ≫ 𝔛.comp κ (toκ.comp ρO) 1 ≫ DRLevel.bcMap ρO toκ =
        pullback.fst _ _ ≫ (comp 𝔛 O ρO κ toκ hϖ H hξ (Sum.inl 1)).subschemeι ≫ toDR 𝔛 O ρO κ toκ hϖ H := by
  unfold toBase toDR D comp
  obtain ⟨n₀⟩ := nonempty_node 𝔛 O ρO hϖ κ toκ H hξ
  haveI : ∀ n, IsReduced (pullback ((C 𝔛 O ρO κ toκ hϖ H).g n) (lamZero 𝔛 O ρO hϖ κ toκ H n)) :=
    fun n => isReduced_pieceZero 𝔛 O ρO hϖ κ toκ H hξ n
  haveI : @Mono Scheme _ _ (C 𝔛 O ρO κ toκ hϖ H).B (iB O) := iB_mono 𝔛 O ρO hϖ κ toκ H hξ
  haveI : Flat (aB 𝔛 O ρO hϖ κ toκ H hξ) := aB_flat 𝔛 O ρO hϖ κ toκ H hξ
  haveI : ∀ n, IsClosedImmersion (lamZero 𝔛 O ρO hϖ κ toκ H n) := fun n => lamZero_isClosedImmersion 𝔛 O ρO hϖ κ toκ H hξ n
  haveI : ∀ n, IsClosedImmersion (lamZero 𝔛 O ρO hϖ κ toκ H n ≫ (C 𝔛 O ρO κ toκ hϖ H).ρ n) :=
    fun n => lamZero_ρ_isClosedImmersion 𝔛 O ρO hϖ κ toκ H hξ n
  obtain ⟨s₀, hs₀⟩ := exists_factor_comp_inl 𝔛 O ρO hϖ κ toκ H hξ 1
  haveI := 𝔛.comp_isClosedImmersion κ (toκ.comp ρO) 1
  haveI := 𝔛.isIntegral_fibre0 (toκ.comp ρO)
  obtain ⟨e, he₁, he₂, he₃⟩ := (C 𝔛 O ρO κ toκ hϖ H).exists_iso_geometricFibre_strictTransform
    (hRF 𝔛 O ρO κ toκ hϖ H) (gRes 𝔛 O ρO κ toκ hϖ H) (hgRes 𝔛 O ρO κ toκ hϖ H)
    (ξ 𝔛 O ρO κ toκ) hξ 1
    (𝔛.comp κ (toκ.comp ρO) 1) (bc (N₀ := N₀) O ρO κ toκ) (pullback.snd _ _) (Spec.map (CommRingCat.ofHom toκ))
    (isPullback_bc 𝔛 O ρO hϖ κ toκ H hξ)
    rfl
    (DRModelPackageLevel.preimage_closure_image_range_comp_eq_of_comp_fst_eq N₀ q hqN 𝔛 O ρO κ toκ (bc (N₀ := N₀) O ρO κ toκ)
      (bc_fst (N₀ := N₀) O ρO κ toκ) 1)
    (IsLocalRing.isClosed_singleton_closedPoint O) (range_bc 𝔛 O ρO hϖ κ toκ H hξ)
    (fun r => πX_bc_apply 𝔛 O ρO hϖ κ toκ H hξ _)
    (lamZero 𝔛 O ρO hϖ κ toκ H) (horientZero_fwd 𝔛 O ρO hϖ κ toκ H hξ) (horientZero_conv 𝔛 O ρO hϖ κ toκ H hξ)
    (x_mem_range_comp1 𝔛 O ρO hϖ κ toκ H hξ)
    n₀ (iB O) (aB 𝔛 O ρO hϖ κ toκ H hξ) (specMap_toκ_eq 𝔛 O ρO hϖ κ toκ H hξ) s₀ hs₀ (hGκ_zero 𝔛 O ρO hϖ κ toκ H hξ n₀)
  refine ⟨e, he₁, ?_, he₃⟩
  rw [← 𝔛.comp_over κ (toκ.comp ρO) 1]
  exact he₂

private theorem strict_iso (i : Fin 2) : ∃ e : pullback ((comp 𝔛 O ρO κ toκ hϖ H hξ (Sum.inl i)).subschemeι ≫ toBase 𝔛 O ρO κ toκ hϖ H)
      (Spec.map (CommRingCat.ofHom toκ)) ⟶ DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO),
    IsIso e ∧ e ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      e ≫ 𝔛.comp κ (toκ.comp ρO) i ≫ DRLevel.bcMap ρO toκ =
        pullback.fst _ _ ≫ (comp 𝔛 O ρO κ toκ hϖ H hξ (Sum.inl i)).subschemeι ≫ toDR 𝔛 O ρO κ toκ hϖ H := by
  obtain rfl | rfl : i = 0 ∨ i = 1 := by revert i; decide
  · exact strict_iso_inf 𝔛 O ρO hϖ κ toκ H hξ
  · exact strict_iso_zero 𝔛 O ρO hϖ κ toκ H hξ

end V3AsmLevel
p2m_reactivate "P2MW.S_V3AsmLevel_strict_iso.MvPolynomial P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme.IdealSheafData"

end
p2m_reactivate "P2MW.S_V3AsmLevel_strict_iso.MvPolynomial P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_strict_iso.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme P2MW.S_V3AsmLevel_strict_iso.AlgebraicGeometry.Scheme.IdealSheafData"

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : ModularCurve.DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : ModularCurve.DRLevel.R q →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (H : V3AsmLevel.SiteHyps 𝔛 O ρO κ toκ) (hξ : ∀ j, V3AsmLevel.ξ 𝔛 O ρO κ toκ j ∈ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).X0)
    (i : Fin 2) :
    ∃ e : pullback ((V3AsmLevel.comp 𝔛 O ρO κ toκ hϖ H hξ (Sum.inl i)).subschemeι ≫ V3AsmLevel.toBase 𝔛 O ρO κ toκ hϖ H)
        (Spec.map (CommRingCat.ofHom toκ)) ⟶ ModularCurve.DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO),
      IsIso e ∧ e ≫ pullback.snd _ _ = pullback.snd _ _ ∧
        e ≫ 𝔛.comp κ (toκ.comp ρO) i ≫ ModularCurve.DRLevel.bcMap ρO toκ =
          pullback.fst _ _ ≫ (V3AsmLevel.comp 𝔛 O ρO κ toκ hϖ H hξ (Sum.inl i)).subschemeι ≫ V3AsmLevel.toDR 𝔛 O ρO κ toκ hϖ H :=
  V3AsmLevel.strict_iso 𝔛 O ρO hϖ κ toκ H hξ i

end S_V3AsmLevel_strict_iso
end P2MW
export P2MW.S_V3AsmLevel_strict_iso (solution)
