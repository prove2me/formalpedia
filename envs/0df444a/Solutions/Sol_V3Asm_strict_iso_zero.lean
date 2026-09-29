-- Prove2me | solution 1 for V3Asm.strict_iso_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/3ce5664b-f548-5a6a-a341-714982964dcb

import Mathlib
import Definitions.Def_ModularCurve_ResolvedModelSite
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_isSeparated
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_iso_hom_comp_eq_of_range_eq
import Theorems.Thm_MvPolynomial_CrossingQuotient_exists_algEquiv_quotient_span_U_and_span_V_polynomial
import Theorems.Thm_ModularCurve_DRModelPackage_preimage_closure_image_range_compInf_eq_of_comp_fst_eq
import Theorems.Thm_ModularCurve_ssJSet_nonempty
import Theorems.Thm_ModularCurve_ssJSet_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_V3Asm_strict_iso_zero
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve"
p2m_attr_erase "instance" "WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"
p2m_attr_erase "simp" "GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false
set_option maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry TopologicalSpace"

universe u

set_option autoImplicit false

noncomputable section

namespace MvPolynomial
p2m_export "MvPolynomial" "X map R zeroLocus ext support algebraMap_apply ringHom_ext comap vanishingIdeal algebraMap_eq C algHom_ext' algHom_ext map_id CrossingQuotient.Resolution CrossingQuotient.U CrossingQuotient.V CrossingQuotient CrossingQuotient.exists_algEquiv_quotient_span_U_and_span_V_polynomial"
p2m_open "MvPolynomial"

namespace CrossingQuotient
p2m_export "MvPolynomial.CrossingQuotient" "crossingScheme Resolution Resolution.ι Resolution.toCrossing Resolution.toSpec U V U_mul_V lift lift_U lift_V resolutionChart resolutionChart_U resolutionChart_V mk mk_surjective Resolution.isSeparated exists_algEquiv_quotient_span_U_and_span_V_polynomial"
p2m_open "MvPolynomial.CrossingQuotient"

variable {W : Type*} [CommRing W] (t : W)

theorem algHom_ext' {A : Type*} [Semiring A] [Algebra W A] {f g : CrossingQuotient W t →ₐ[W] A}
    (hU : f (U t) = g (U t)) (hV : f (V t) = g (V t)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · exact hU
  · exact hV

theorem algebraMap_mem_span_V' : algebraMap W (CrossingQuotient W t) t ∈ Ideal.span {V t} := by
  rw [← U_mul_V]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

theorem algebraMap_mem_span_U' : algebraMap W (CrossingQuotient W t) t ∈ Ideal.span {U t} := by
  rw [← U_mul_V]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

abbrev strictVIdeal (e : ℕ) : Ideal (CrossingQuotient W (t ^ e)) :=
  Ideal.span {V (t ^ e), algebraMap W (CrossingQuotient W (t ^ e)) t}

abbrev strictUIdeal (e : ℕ) : Ideal (CrossingQuotient W (t ^ e)) :=
  Ideal.span {U (t ^ e), algebraMap W (CrossingQuotient W (t ^ e)) t}

theorem algebraMap_mem_strictVIdeal (e : ℕ) : algebraMap W (CrossingQuotient W (t ^ e)) t ∈ strictVIdeal t e :=
  Ideal.subset_span (Or.inr rfl)

theorem algebraMap_mem_strictUIdeal (e : ℕ) : algebraMap W (CrossingQuotient W (t ^ e)) t ∈ strictUIdeal t e :=
  Ideal.subset_span (Or.inr rfl)

section chartZero

variable (e : ℕ)

theorem strictVIdeal_le_ker (he : 0 < e) :
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

def strictZeroHom (he : 0 < e) :
    (CrossingQuotient W (t ^ e) ⧸ strictVIdeal t e) →ₐ[W] (CrossingQuotient W t ⧸ Ideal.span {V t}) :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ W (Ideal.span {V t})).comp (resolutionChart t e ⟨0, he⟩))
    (fun _ ha => (RingHom.mem_ker).mp (strictVIdeal_le_ker t e he ha))

theorem strictZeroHom_mk (he : 0 < e) (a : CrossingQuotient W (t ^ e)) :
    strictZeroHom t e he (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (resolutionChart t e ⟨0, he⟩ a) := rfl

theorem mk_algebraMap_eq_zero : Ideal.Quotient.mk (strictVIdeal t e) (algebraMap W _ t) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (algebraMap_mem_strictVIdeal t e)

theorem quot_mul_zero (x : CrossingQuotient W (t ^ e) ⧸ strictVIdeal t e) : x * 0 = 0 := mul_zero x

theorem mk_U_mul_zero :
    Ideal.Quotient.mk (strictVIdeal t e) (U (t ^ e)) * 0 =
      Ideal.Quotient.mk (strictVIdeal t e) (algebraMap W (CrossingQuotient W (t ^ e)) t) := by
  rw [quot_mul_zero, mk_algebraMap_eq_zero]

def strictZeroInv :
    (CrossingQuotient W t ⧸ Ideal.span {V t}) →ₐ[W] (CrossingQuotient W (t ^ e) ⧸ strictVIdeal t e) :=
  Ideal.Quotient.liftₐ _ (lift t (Ideal.Quotient.mk _ (U (t ^ e))) 0 (mk_U_mul_zero t e))
    (by
      intro a ha
      rw [Ideal.mem_span_singleton'] at ha
      obtain ⟨b, rfl⟩ := ha
      rw [map_mul, lift_V]
      exact quot_mul_zero t e _)

theorem strictZeroInv_mk_U :
    strictZeroInv t e (Ideal.Quotient.mk _ (U t)) = Ideal.Quotient.mk _ (U (t ^ e)) := by
  change lift t (Ideal.Quotient.mk _ (U (t ^ e))) 0 (mk_U_mul_zero t e) (U t) = _
  rw [lift_U]

theorem strictZeroInv_mk_V : strictZeroInv t e (Ideal.Quotient.mk _ (V t)) = 0 := by
  change lift t (Ideal.Quotient.mk _ (U (t ^ e))) 0 (mk_U_mul_zero t e) (V t) = _
  rw [lift_V]

theorem strictZeroInv_comp_strictZeroHom (he : 0 < e) :
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

theorem strictZeroHom_comp_strictZeroInv (he : 0 < e) :
    (strictZeroHom t e he).comp (strictZeroInv t e) = AlgHom.id W _ := by
  apply Ideal.Quotient.algHom_ext
  apply algHom_ext' t
  · change strictZeroHom t e he (strictZeroInv t e (Ideal.Quotient.mk _ (U t))) = Ideal.Quotient.mk _ (U t)
    rw [strictZeroInv_mk_U, strictZeroHom_mk, resolutionChart_U]
    simp only [pow_zero, map_one, one_mul]
  · change strictZeroHom t e he (strictZeroInv t e (Ideal.Quotient.mk _ (V t))) = Ideal.Quotient.mk _ (V t)
    rw [strictZeroInv_mk_V, map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl

def strictZeroEquiv (he : 0 < e) :
    (CrossingQuotient W (t ^ e) ⧸ strictVIdeal t e) ≃ₐ[W] (CrossingQuotient W t ⧸ Ideal.span {V t}) :=
  AlgEquiv.ofAlgHom (strictZeroHom t e he) (strictZeroInv t e)
    (strictZeroHom_comp_strictZeroInv t e he) (strictZeroInv_comp_strictZeroHom t e he)

theorem exists_algEquiv_comp_mk_eq_mk_comp_resolutionChart_zero (he : 0 < e) :
    ∃ E : (CrossingQuotient W (t ^ e) ⧸ strictVIdeal t e) ≃ₐ[W] (CrossingQuotient W t ⧸ Ideal.span {V t}),
      E.toAlgHom.comp (Ideal.Quotient.mkₐ W _) =
        (Ideal.Quotient.mkₐ W (Ideal.span {V t})).comp (resolutionChart t e ⟨0, he⟩) :=
  ⟨strictZeroEquiv t e he, Ideal.Quotient.algHom_ext _ rfl⟩

theorem mk_comp_resolutionChart_zero_surjective (he : 0 < e) :
    Function.Surjective ((Ideal.Quotient.mkₐ W (Ideal.span {V t})).comp (resolutionChart t e ⟨0, he⟩)) := by
  intro z
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((strictZeroEquiv t e he).symm z)
  refine ⟨a, ?_⟩
  change (strictZeroEquiv t e he) (Ideal.Quotient.mk _ a) = z
  rw [ha, AlgEquiv.apply_symm_apply]

theorem ker_mk_comp_resolutionChart_zero (he : 0 < e) :
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

abbrev lastIdx (he : 0 < e) : Fin e := ⟨e - 1, Nat.sub_one_lt_of_lt he⟩

theorem resolutionChart_last_V (he : 0 < e) : resolutionChart t e (lastIdx e he) (V (t ^ e)) = V t := by
  rw [resolutionChart_V]
  simp only [Nat.sub_self, pow_zero, map_one, one_mul]

theorem strictUIdeal_le_ker (he : 0 < e) :
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

def strictLastHom (he : 0 < e) :
    (CrossingQuotient W (t ^ e) ⧸ strictUIdeal t e) →ₐ[W] (CrossingQuotient W t ⧸ Ideal.span {U t}) :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ W (Ideal.span {U t})).comp (resolutionChart t e (lastIdx e he)))
    (fun _ ha => (RingHom.mem_ker).mp (strictUIdeal_le_ker t e he ha))

theorem strictLastHom_mk (he : 0 < e) (a : CrossingQuotient W (t ^ e)) :
    strictLastHom t e he (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (resolutionChart t e (lastIdx e he) a) := rfl

theorem mk_algebraMap_eq_zero' : Ideal.Quotient.mk (strictUIdeal t e) (algebraMap W _ t) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (algebraMap_mem_strictUIdeal t e)

theorem quot_zero_mul (x : CrossingQuotient W (t ^ e) ⧸ strictUIdeal t e) : 0 * x = 0 := zero_mul x

theorem quot_mul_zero' (x : CrossingQuotient W (t ^ e) ⧸ strictUIdeal t e) : x * 0 = 0 := mul_zero x

theorem zero_mul_mk_V :
    0 * Ideal.Quotient.mk (strictUIdeal t e) (V (t ^ e)) =
      Ideal.Quotient.mk (strictUIdeal t e) (algebraMap W (CrossingQuotient W (t ^ e)) t) := by
  rw [quot_zero_mul, mk_algebraMap_eq_zero']

def strictLastInv :
    (CrossingQuotient W t ⧸ Ideal.span {U t}) →ₐ[W] (CrossingQuotient W (t ^ e) ⧸ strictUIdeal t e) :=
  Ideal.Quotient.liftₐ _ (lift t 0 (Ideal.Quotient.mk _ (V (t ^ e))) (zero_mul_mk_V t e))
    (by
      intro a ha
      rw [Ideal.mem_span_singleton'] at ha
      obtain ⟨b, rfl⟩ := ha
      rw [map_mul, lift_U]
      exact quot_mul_zero' t e _)

theorem strictLastInv_mk_V :
    strictLastInv t e (Ideal.Quotient.mk _ (V t)) = Ideal.Quotient.mk _ (V (t ^ e)) := by
  change lift t 0 (Ideal.Quotient.mk _ (V (t ^ e))) (zero_mul_mk_V t e) (V t) = _
  rw [lift_V]

theorem strictLastInv_mk_U : strictLastInv t e (Ideal.Quotient.mk _ (U t)) = 0 := by
  change lift t 0 (Ideal.Quotient.mk _ (V (t ^ e))) (zero_mul_mk_V t e) (U t) = _
  rw [lift_U]

theorem strictLastInv_comp_strictLastHom (he : 0 < e) :
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

theorem strictLastHom_comp_strictLastInv (he : 0 < e) :
    (strictLastHom t e he).comp (strictLastInv t e) = AlgHom.id W _ := by
  apply Ideal.Quotient.algHom_ext
  apply algHom_ext' t
  · change strictLastHom t e he (strictLastInv t e (Ideal.Quotient.mk _ (U t))) = Ideal.Quotient.mk _ (U t)
    rw [strictLastInv_mk_U, map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  · change strictLastHom t e he (strictLastInv t e (Ideal.Quotient.mk _ (V t))) = Ideal.Quotient.mk _ (V t)
    rw [strictLastInv_mk_V, strictLastHom_mk, resolutionChart_last_V]

def strictLastEquiv (he : 0 < e) :
    (CrossingQuotient W (t ^ e) ⧸ strictUIdeal t e) ≃ₐ[W] (CrossingQuotient W t ⧸ Ideal.span {U t}) :=
  AlgEquiv.ofAlgHom (strictLastHom t e he) (strictLastInv t e)
    (strictLastHom_comp_strictLastInv t e he) (strictLastInv_comp_strictLastHom t e he)

theorem exists_algEquiv_comp_mk_eq_mk_comp_resolutionChart_last (he : 0 < e) :
    ∃ E : (CrossingQuotient W (t ^ e) ⧸ strictUIdeal t e) ≃ₐ[W] (CrossingQuotient W t ⧸ Ideal.span {U t}),
      E.toAlgHom.comp (Ideal.Quotient.mkₐ W _) =
        (Ideal.Quotient.mkₐ W (Ideal.span {U t})).comp (resolutionChart t e (lastIdx e he)) :=
  ⟨strictLastEquiv t e he, Ideal.Quotient.algHom_ext _ rfl⟩

theorem mk_comp_resolutionChart_last_surjective (he : 0 < e) :
    Function.Surjective ((Ideal.Quotient.mkₐ W (Ideal.span {U t})).comp (resolutionChart t e (lastIdx e he))) := by
  intro z
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((strictLastEquiv t e he).symm z)
  refine ⟨a, ?_⟩
  change (strictLastEquiv t e he) (Ideal.Quotient.mk _ a) = z
  rw [ha, AlgEquiv.apply_symm_apply]

theorem ker_mk_comp_resolutionChart_last (he : 0 < e) :
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
p2m_export "MvPolynomial.CrossingQuotient" "crossingScheme Resolution Resolution.ι Resolution.toCrossing Resolution.toSpec U V U_mul_V lift lift_U lift_V resolutionChart resolutionChart_U resolutionChart_V mk mk_surjective Resolution.isSeparated exists_algEquiv_quotient_span_U_and_span_V_polynomial"
namespace Resolution
p2m_export "MvPolynomial.CrossingQuotient.Resolution" "ι openCover toCrossing ι_toCrossing toSpec ι_toSpec hom_ext isSeparated"
p2m_open "MvPolynomial.CrossingQuotient.Resolution MvPolynomial.CrossingQuotient MvPolynomial"

p2m_open "AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry CategoryTheory"

universe v

variable {W : Type v} [CommRing W] (t : W) (e : ℕ)

theorem isSeparated_toCrossing' : IsSeparated (Resolution.toCrossing t e) :=
  (Resolution.isSeparated t e).2

def strictVι (he : 0 < e) :
    Spec (CommRingCat.of (CrossingQuotient W t ⧸ Ideal.span {V t})) ⟶ Resolution t e :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {V t}))) ≫ Resolution.ι t e ⟨0, he⟩

def strictUι (he : 0 < e) :
    Spec (CommRingCat.of (CrossingQuotient W t ⧸ Ideal.span {U t})) ⟶ Resolution t e :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {U t}))) ≫ Resolution.ι t e (lastIdx e he)

theorem strictVι_toCrossing (he : 0 < e) :
    strictVι t e he ≫ toCrossing t e = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mkₐ W (Ideal.span {V t})).comp (resolutionChart t e ⟨0, he⟩)).toRingHom) := by
  rw [strictVι, Category.assoc, ι_toCrossing, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem strictUι_toCrossing (he : 0 < e) :
    strictUι t e he ≫ toCrossing t e = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mkₐ W (Ideal.span {U t})).comp (resolutionChart t e (lastIdx e he))).toRingHom) := by
  rw [strictUι, Category.assoc, ι_toCrossing, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

scoped instance isClosedImmersion_strictVι_toCrossing (he : 0 < e) : IsClosedImmersion (strictVι t e he ≫ toCrossing t e) := by
  rw [strictVι_toCrossing]
  exact IsClosedImmersion.spec_of_surjective _ (mk_comp_resolutionChart_zero_surjective t e he)

scoped instance isClosedImmersion_strictUι_toCrossing (he : 0 < e) : IsClosedImmersion (strictUι t e he ≫ toCrossing t e) := by
  rw [strictUι_toCrossing]
  exact IsClosedImmersion.spec_of_surjective _ (mk_comp_resolutionChart_last_surjective t e he)

scoped instance isClosedImmersion_strictVι (he : 0 < e) : IsClosedImmersion (strictVι t e he) :=
  haveI := isSeparated_toCrossing' t e
  IsClosedImmersion.of_comp (strictVι t e he) (toCrossing t e)

scoped instance isClosedImmersion_strictUι (he : 0 < e) : IsClosedImmersion (strictUι t e he) :=
  haveI := isSeparated_toCrossing' t e
  IsClosedImmersion.of_comp (strictUι t e he) (toCrossing t e)

theorem range_strictVι_toCrossing (he : 0 < e) :
    Set.range (strictVι t e he ≫ toCrossing t e).base = PrimeSpectrum.zeroLocus (strictVIdeal t e : Set (CrossingQuotient W (t ^ e))) := by
  rw [strictVι_toCrossing, ← ker_mk_comp_resolutionChart_zero t e he, Spec.map_base]
  exact _root_.range_comap_of_surjective _ _ (mk_comp_resolutionChart_zero_surjective t e he)

theorem range_strictUι_toCrossing (he : 0 < e) :
    Set.range (strictUι t e he ≫ toCrossing t e).base = PrimeSpectrum.zeroLocus (strictUIdeal t e : Set (CrossingQuotient W (t ^ e))) := by
  rw [strictUι_toCrossing, ← ker_mk_comp_resolutionChart_last t e he, Spec.map_base]
  exact _root_.range_comap_of_surjective _ _ (mk_comp_resolutionChart_last_surjective t e he)

theorem mem_zeroLocus_strictVIdeal_iff (P : PrimeSpectrum (CrossingQuotient W (t ^ e))) :
    P ∈ PrimeSpectrum.zeroLocus (strictVIdeal t e : Set (CrossingQuotient W (t ^ e))) ↔
      V (t ^ e) ∈ P.asIdeal ∧ algebraMap W _ t ∈ P.asIdeal := by
  rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  rfl

theorem mem_zeroLocus_strictUIdeal_iff (P : PrimeSpectrum (CrossingQuotient W (t ^ e))) :
    P ∈ PrimeSpectrum.zeroLocus (strictUIdeal t e : Set (CrossingQuotient W (t ^ e))) ↔
      U (t ^ e) ∈ P.asIdeal ∧ algebraMap W _ t ∈ P.asIdeal := by
  rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  rfl

theorem algebraMap_mem_of_V_mem (P : PrimeSpectrum (CrossingQuotient W (t ^ e)))
    (hV : V (t ^ e) ∈ P.asIdeal) : algebraMap W _ t ∈ P.asIdeal := by
  apply P.isPrime.mem_of_pow_mem e
  rw [← map_pow, ← U_mul_V]
  exact P.asIdeal.mul_mem_left _ hV

theorem algebraMap_mem_of_U_mem (P : PrimeSpectrum (CrossingQuotient W (t ^ e)))
    (hU : U (t ^ e) ∈ P.asIdeal) : algebraMap W _ t ∈ P.asIdeal := by
  apply P.isPrime.mem_of_pow_mem e
  rw [← map_pow, ← U_mul_V]
  exact P.asIdeal.mul_mem_right _ hU

theorem mem_range_strictVι_toCrossing_iff (he : 0 < e) (P : PrimeSpectrum (CrossingQuotient W (t ^ e))) :
    P ∈ Set.range (strictVι t e he ≫ toCrossing t e).base ↔ V (t ^ e) ∈ P.asIdeal := by
  have h1 : P ∈ Set.range (strictVι t e he ≫ toCrossing t e).base ↔
      P ∈ PrimeSpectrum.zeroLocus (strictVIdeal t e : Set (CrossingQuotient W (t ^ e))) := by
    rw [range_strictVι_toCrossing]
    exact Iff.rfl
  exact h1.trans ((mem_zeroLocus_strictVIdeal_iff t e P).trans
    ⟨fun h => h.1, fun h => ⟨h, algebraMap_mem_of_V_mem t e P h⟩⟩)

theorem mem_range_strictUι_toCrossing_iff (he : 0 < e) (P : PrimeSpectrum (CrossingQuotient W (t ^ e))) :
    P ∈ Set.range (strictUι t e he ≫ toCrossing t e).base ↔ U (t ^ e) ∈ P.asIdeal := by
  have h1 : P ∈ Set.range (strictUι t e he ≫ toCrossing t e).base ↔
      P ∈ PrimeSpectrum.zeroLocus (strictUIdeal t e : Set (CrossingQuotient W (t ^ e))) := by
    rw [range_strictUι_toCrossing]
    exact Iff.rfl
  exact h1.trans ((mem_zeroLocus_strictUIdeal_iff t e P).trans
    ⟨fun h => h.1, fun h => ⟨h, algebraMap_mem_of_U_mem t e P h⟩⟩)

end MvPolynomial.CrossingQuotient.Resolution
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution"
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient"
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial"

end
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry TopologicalSpace Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective IsClosedImmersion.of_comp basicOpen_eq_bot_iff Scheme.Hom iSup_affineOpens_eq_top Scheme.Pullback.range_fst isPullback_morphismRestrict IsZariskiLocalAtTarget LocallyOfFiniteType Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme pullbackSpecIso IsOpenImmersion Spec.map_base Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced IsSeparated HasRingHomProperty.appLE SpecMap_ΓSpecIso_hom isAffineOpen_top Scheme.basicOpen_appLE Scheme.preimage_basicOpen_top Spec.map_id IsZariskiLocalAtTarget.of_iSup_eq_top Etale Scheme.Spec affine_isIntegral_iff FormallyUnramified isReduced_of_isOpenImmersion Scheme.Pullback.exists_preimage_pullback isReduced_of_isAffine_isReduced HasRingHomProperty Etale.iff_flat_and_formallyUnramified toSpecΓ basicOpen_eq_of_affine geometrically range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq"
p2m_open "AlgebraicGeometry"

namespace RingHom.Flat

private theorem _root_.AlgebraicGeometry.RingHom.Flat.map_mem_nonZeroDivisors {A B : Type*} [CommRing A] [CommRing B] {φ : A →+* B}
    (hφ : φ.Flat) {r : A} (hr : r ∈ nonZeroDivisors A) : φ r ∈ nonZeroDivisors B := by
  letI := φ.toAlgebra
  haveI : Module.Flat A B := hφ
  have hsm : IsSMulRegular B r := Module.Flat.isSMulRegular_of_nonZeroDivisors hr
  have key : ∀ x : B, φ r * x = 0 → x = 0 := fun x hx =>
    hsm ((Algebra.smul_def r x).trans (hx.trans (smul_zero r).symm))
  exact mem_nonZeroDivisors_iff.mpr ⟨key, fun x hx => key x ((mul_comm _ _).trans hx)⟩

end RingHom.Flat
p2m_export "AlgebraicGeometry" "RingHom.Flat.map_mem_nonZeroDivisors"
section

variable {T S Z : Scheme.{u}} (π : T ⟶ S) [Flat π] [IsIntegral S]
  (V : S.Opens) (hV : (V : Set S).Nonempty)
  (j : Z ⟶ T) [IsOpenImmersion j] [IsReduced Z] (hj : π ⁻¹ᵁ V ≤ j.opensRange)

include hV hj in

theorem isReduced_presheaf_obj_of_flat_of_le_preimage
    (W : S.affineOpens) (Q : T.affineOpens) (hle : (Q : T.Opens) ≤ π ⁻¹ᵁ (W : S.Opens))
    (hQ : ((Q : T.Opens) : Set T).Nonempty) :
    _root_.IsReduced Γ(T, Q) := by

  obtain ⟨t, ht⟩ := hQ
  haveI : Nonempty (W : S.Opens) := ⟨⟨π.base t, hle ht⟩⟩
  haveI : IsDomain Γ(S, W) := inferInstance

  obtain ⟨w, hwW, hwV⟩ : ((W : S.Opens) ⊓ V : S.Opens).1.Nonempty :=
    nonempty_preirreducible_inter (W : S.Opens).2 V.2 ⟨π.base t, hle ht⟩ hV
  obtain ⟨r, hrV, hwr⟩ := W.2.exists_basicOpen_le ⟨w, hwV⟩ hwW
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hwr
    exact hwr
  have hr : r ∈ nonZeroDivisors Γ(S, W) := mem_nonZeroDivisors_of_ne_zero hr0

  let φ := π.appLE W Q hle
  have hφ : φ.hom.Flat := HasRingHomProperty.appLE (P := @Flat) (f := π) inferInstance W Q hle
  set s : Γ(T, Q) := φ.hom r with hs
  have hsreg : s ∈ nonZeroDivisors Γ(T, Q) := hφ.map_mem_nonZeroDivisors hr

  haveI := Q.2.isLocalization_basicOpen s
  have hinj : Function.Injective (algebraMap Γ(T, Q) Γ(T, T.basicOpen s)) :=
    IsLocalization.injective (M := Submonoid.powers s) _ ((Submonoid.powers_le).mpr hsreg)

  have hbo : T.basicOpen s ≤ π ⁻¹ᵁ V := by
    have h1 : T.basicOpen s = (Q : T.Opens) ⊓ π ⁻¹ᵁ (S.basicOpen r) := by
      rw [hs]
      exact Scheme.basicOpen_appLE π (Q : T.Opens) (W : S.Opens) hle r
    rw [h1]
    exact inf_le_right.trans (fun x hx => hrV hx)
  have hbo' : T.basicOpen s ≤ j.opensRange := hbo.trans hj
  haveI : _root_.IsReduced Γ(T, T.basicOpen s) := by
    have e : Γ(T, T.basicOpen s) ≅ Γ(Z, j ⁻¹ᵁ (T.basicOpen s)) := by
      have h1 : j ''ᵁ (j ⁻¹ᵁ (T.basicOpen s)) = T.basicOpen s := by
        ext1
        change j.base '' (j.base ⁻¹' (T.basicOpen s : Set T)) = (T.basicOpen s : Set T)
        rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left]
        exact fun x hx => hbo' hx
      exact (T.presheaf.mapIso (eqToIso h1).op) ≪≫ (j.appIso (j ⁻¹ᵁ (T.basicOpen s)))
    exact isReduced_of_injective e.commRingCatIsoToRingEquiv e.commRingCatIsoToRingEquiv.injective
  exact isReduced_of_injective _ hinj

include hV hj in

theorem isReduced_of_flat_of_isReduced_preimage : IsReduced T := by
  have key : ∀ t : T, ∃ (W : S.affineOpens) (Q : T.affineOpens),
      t ∈ (Q : T.Opens) ∧ (Q : T.Opens) ≤ π ⁻¹ᵁ (W : S.Opens) := by
    intro t
    obtain ⟨W, hWB, htW, -⟩ := (Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
      (show π.base t ∈ (⊤ : S.Opens) from trivial)
    obtain ⟨Q, hQB, htQ, hQle⟩ := (Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens)
      (show t ∈ π ⁻¹ᵁ W from htW)
    exact ⟨⟨W, hWB⟩, ⟨Q, hQB⟩, htQ, hQle⟩
  choose W Q htQ hQle using key
  have hcov : ⨆ t : T, (Q t : T.Opens) = ⊤ := eq_top_iff.mpr fun t _ => Opens.mem_iSup.mpr ⟨t, htQ t⟩
  haveI : ∀ t : T, IsReduced ((T.openCoverOfIsOpenCover (fun t : T => ((Q t : T.Opens) : T.Opens)) hcov).X t) :=
    fun t => by
      change IsReduced ((Q t : T.Opens) : Scheme.{u})
      haveI : _root_.IsReduced Γ(T, Q t) :=
        isReduced_presheaf_obj_of_flat_of_le_preimage π V hV j hj (W t) (Q t) (hQle t) ⟨t, htQ t⟩
      haveI : _root_.IsReduced Γ((Q t : T.Opens), ⊤) :=
        isReduced_of_injective (Q t : T.Opens).topIso.commRingCatIsoToRingEquiv
          (Q t : T.Opens).topIso.commRingCatIsoToRingEquiv.injective
      exact isReduced_of_isAffine_isReduced _
  exact IsReduced.of_openCover _ (T.openCoverOfIsOpenCover (fun t : T => ((Q t : T.Opens) : T.Opens)) hcov)

end
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution"

end AlgebraicGeometry
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective IsClosedImmersion.of_comp basicOpen_eq_bot_iff Scheme.Hom iSup_affineOpens_eq_top Scheme.Pullback.range_fst isPullback_morphismRestrict IsZariskiLocalAtTarget LocallyOfFiniteType Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme pullbackSpecIso IsOpenImmersion Spec.map_base Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced IsSeparated HasRingHomProperty.appLE SpecMap_ΓSpecIso_hom isAffineOpen_top Scheme.basicOpen_appLE Scheme.preimage_basicOpen_top Spec.map_id IsZariskiLocalAtTarget.of_iSup_eq_top Etale Scheme.Spec affine_isIntegral_iff FormallyUnramified isReduced_of_isOpenImmersion Scheme.Pullback.exists_preimage_pullback isReduced_of_isAffine_isReduced HasRingHomProperty Etale.iff_flat_and_formallyUnramified toSpecΓ basicOpen_eq_of_affine geometrically range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq"
p2m_open "AlgebraicGeometry"

section monoPullback

variable {C : Type*} [Category C] {S A B Z : C} (s : S ⟶ B) (a : A ⟶ B) (i : B ⟶ Z) [Mono i]
  [HasPullback s a] [HasPullback (s ≫ i) (a ≫ i)]

noncomputable def pullbackCompMonoIso : pullback (s ≫ i) (a ≫ i) ≅ pullback s a where
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
theorem pullbackCompMonoIso_hom_fst : (pullbackCompMonoIso s a i).hom ≫ pullback.fst s a = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

@[scoped simp, reassoc]
theorem pullbackCompMonoIso_hom_snd : (pullbackCompMonoIso s a i).hom ≫ pullback.snd s a = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

@[scoped simp, reassoc]
theorem pullbackCompMonoIso_inv_fst : (pullbackCompMonoIso s a i).inv ≫ pullback.fst _ _ = pullback.fst s a :=
  pullback.lift_fst _ _ _

@[scoped simp, reassoc]
theorem pullbackCompMonoIso_inv_snd : (pullbackCompMonoIso s a i).inv ≫ pullback.snd _ _ = pullback.snd s a :=
  pullback.lift_snd _ _ _

end monoPullback
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution"

theorem flat_pullback_fst_comp_mono {S A B Z : Scheme.{u}} (s : S ⟶ B) (a : A ⟶ B) (i : B ⟶ Z) [Mono i] [Flat a] :
    Flat (pullback.fst (s ≫ i) (a ≫ i)) := by
  rw [← pullbackCompMonoIso_hom_fst s a i]
  infer_instance

section factor

variable {S : Scheme.{u}} {O : Type u} [CommRing O] (f : S ⟶ Spec (CommRingCat.of O)) (I : Ideal O)

noncomputable def toΓ : O →+* Γ(S, ⊤) :=
  (f.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom

theorem toΓ_apply (r : O) : toΓ f r = f.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv r) := rfl

theorem toΓ_eq_zero_of_preimage_basicOpen_eq_bot [IsReduced S] (r : O)
    (hr : f ⁻¹ᵁ (PrimeSpectrum.basicOpen r : (Spec (CommRingCat.of O)).Opens) = ⊥) : toΓ f r = 0 := by
  rw [← basicOpen_eq_bot_iff, toΓ_apply, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  exact hr

variable (hI : ∀ r ∈ I, f ⁻¹ᵁ (PrimeSpectrum.basicOpen r : (Spec (CommRingCat.of O)).Opens) = ⊥)

include hI in

theorem exists_lift_specQuotient [IsReduced S] :
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
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution"

end AlgebraicGeometry
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective IsClosedImmersion.of_comp basicOpen_eq_bot_iff Scheme.Hom iSup_affineOpens_eq_top Scheme.Pullback.range_fst isPullback_morphismRestrict IsZariskiLocalAtTarget LocallyOfFiniteType Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme pullbackSpecIso IsOpenImmersion Spec.map_base Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced IsSeparated HasRingHomProperty.appLE SpecMap_ΓSpecIso_hom isAffineOpen_top Scheme.basicOpen_appLE Scheme.preimage_basicOpen_top Spec.map_id IsZariskiLocalAtTarget.of_iSup_eq_top Etale Scheme.Spec affine_isIntegral_iff FormallyUnramified isReduced_of_isOpenImmersion Scheme.Pullback.exists_preimage_pullback isReduced_of_isAffine_isReduced HasRingHomProperty Etale.iff_flat_and_formallyUnramified toSpecΓ basicOpen_eq_of_affine geometrically range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq"
p2m_open "AlgebraicGeometry"

section basechange

variable {X S S' S'' : Scheme.{u}} (f : X ⟶ S) (g' : S' ⟶ S) (g'' : S'' ⟶ S) (i : S'' ⟶ S') (hi : i ≫ g' = g'')

theorem isPullback_map_snd_snd :
    IsPullback (pullback.map f g'' f g' (𝟙 X) i (𝟙 S) (by simp) (by rw [Category.comp_id, hi]))
      (pullback.snd f g'') (pullback.snd f g') i := by
  refine IsPullback.of_right (h₁₂ := pullback.fst f g') (v₁₃ := f) (h₂₂ := g') ?_ ?_ (IsPullback.of_hasPullback f g')
  · rw [pullback.lift_fst, Category.comp_id, hi]
    exact IsPullback.of_hasPullback f g''
  · rw [pullback.lift_snd]

end basechange
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry"

section strict

variable {S Y X Xκ B Bκ R : Scheme.{u}}

theorem exists_iso_pullback_of_isClosedImmersion_of_preimage_range_eq
    (ιS : S ⟶ Y) (toDR : Y ⟶ X) (πX : X ⟶ B) (toBase : Y ⟶ B) (hbase : toDR ≫ πX = toBase)
    (b : Bκ ⟶ B) (p₁ : Xκ ⟶ X) (p₂ : Xκ ⟶ Bκ) (hP : IsPullback p₁ p₂ πX b)
    (c : R ⟶ Xκ) [IsClosedImmersion c] [IsReduced R] [IsClosedImmersion (ιS ≫ toDR)]
    (hrange : p₁.base ⁻¹' Set.range (ιS ≫ toDR).base = Set.range c.base)
    [IsReduced (pullback (ιS ≫ toBase) b)] :
    ∃ e : pullback (ιS ≫ toBase) b ⟶ R,
      IsIso e ∧ e ≫ c ≫ p₂ = pullback.snd _ _ ∧ e ≫ c ≫ p₁ = pullback.fst _ _ ≫ ιS ≫ toDR := by

  have hw : (pullback.fst (ιS ≫ toBase) b ≫ ιS ≫ toDR) ≫ πX = pullback.snd (ιS ≫ toBase) b ≫ b := by
    simp only [Category.assoc, hbase]
    exact pullback.condition
  let τ : pullback (ιS ≫ toBase) b ⟶ Xκ := hP.lift (pullback.fst _ _ ≫ ιS ≫ toDR) (pullback.snd _ _) hw
  have hτ₁ : τ ≫ p₁ = pullback.fst _ _ ≫ ιS ≫ toDR := hP.lift_fst _ _ _
  have hτ₂ : τ ≫ p₂ = pullback.snd _ _ := hP.lift_snd _ _ _

  let u : pullback (ιS ≫ toBase) b ⟶ pullback (ιS ≫ toDR) p₁ := pullback.lift (pullback.fst _ _) τ hτ₁.symm
  have hv : pullback.fst (ιS ≫ toDR) p₁ ≫ ιS ≫ toBase = (pullback.snd (ιS ≫ toDR) p₁ ≫ p₂) ≫ b := by
    rw [← hbase, Category.assoc, ← hP.w, ← Category.assoc (pullback.snd _ _), ← pullback.condition,
      Category.assoc, Category.assoc]
  let v : pullback (ιS ≫ toDR) p₁ ⟶ pullback (ιS ≫ toBase) b :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ p₂) hv
  have hvτ : v ≫ τ = pullback.snd (ιS ≫ toDR) p₁ := by
    apply hP.hom_ext
    · rw [Category.assoc, hτ₁, ← Category.assoc, pullback.lift_fst, pullback.condition]
    · rw [Category.assoc, hτ₂, pullback.lift_snd]
  have huv : u ≫ v = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, hτ₂, Category.id_comp]
  have hvu : v ≫ u = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, hvτ, Category.id_comp]
  haveI : IsIso u := ⟨⟨v, huv, hvu⟩⟩
  have hu : u ≫ pullback.snd (ιS ≫ toDR) p₁ = τ := pullback.lift_snd _ _ _

  haveI : IsClosedImmersion τ := by rw [← hu]; infer_instance
  have hsurj : Function.Surjective u.base := u.homeomorph.surjective
  have hτrange : Set.range τ.base = Set.range c.base := by
    rw [← hrange, ← hu, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr hsurj, Set.image_univ, Scheme.Pullback.range_snd]
  obtain ⟨e, he⟩ := IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq τ c hτrange
  exact ⟨e.hom, inferInstance, by rw [← Category.assoc, he, hτ₂], by rw [← Category.assoc, he, hτ₁]⟩

end strict
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry"

section chart

variable {U Se Res F : Scheme.{u}} (f : U ⟶ Se) (ρ : Res ⟶ Se) (lam : F ⟶ Res)

theorem pullback_fst_snd_comp_fst_eq :
    pullback.fst (pullback.snd f ρ) lam ≫ pullback.fst f ρ =
      (pullbackLeftPullbackSndIso f ρ lam).hom ≫ pullback.fst f (lam ≫ ρ) := by
  rw [pullbackLeftPullbackSndIso_hom_fst]

scoped instance isClosedImmersion_pullback_fst_snd_comp_fst [IsClosedImmersion (lam ≫ ρ)] :
    IsClosedImmersion (pullback.fst (pullback.snd f ρ) lam ≫ pullback.fst f ρ) := by
  rw [pullback_fst_snd_comp_fst_eq]
  infer_instance

theorem range_pullback_fst_snd_comp_fst :
    Set.range (pullback.fst (pullback.snd f ρ) lam ≫ pullback.fst f ρ).base =
      f.base ⁻¹' Set.range (lam ≫ ρ).base := by
  have hsurj : Function.Surjective (pullbackLeftPullbackSndIso f ρ lam).hom.base :=
    (pullbackLeftPullbackSndIso f ρ lam).hom.homeomorph.surjective
  rw [pullback_fst_snd_comp_fst_eq, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr hsurj, Set.image_univ, Scheme.Pullback.range_fst]

scoped instance etale_pullback_snd_snd [Etale f] : Etale (pullback.snd (pullback.snd f ρ) lam) := by
  have : pullback.snd (pullback.snd f ρ) lam = (pullbackLeftPullbackSndIso f ρ lam).hom ≫ pullback.snd f (lam ≫ ρ) := by
    rw [pullbackLeftPullbackSndIso_hom_snd]
  rw [this]
  infer_instance

end chart
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry"

end AlgebraicGeometry
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry"

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective IsClosedImmersion.of_comp basicOpen_eq_bot_iff Scheme.Hom iSup_affineOpens_eq_top Scheme.Pullback.range_fst isPullback_morphismRestrict IsZariskiLocalAtTarget LocallyOfFiniteType Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme pullbackSpecIso IsOpenImmersion Spec.map_base Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced IsSeparated HasRingHomProperty.appLE SpecMap_ΓSpecIso_hom isAffineOpen_top Scheme.basicOpen_appLE Scheme.preimage_basicOpen_top Spec.map_id IsZariskiLocalAtTarget.of_iSup_eq_top Etale Scheme.Spec affine_isIntegral_iff FormallyUnramified isReduced_of_isOpenImmersion Scheme.Pullback.exists_preimage_pullback isReduced_of_isAffine_isReduced HasRingHomProperty Etale.iff_flat_and_formallyUnramified toSpecΓ basicOpen_eq_of_affine geometrically range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq"
p2m_open "AlgebraicGeometry"

end AlgebraicGeometry
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry"

namespace V3Glue
p2m_export "V3Glue" "Site.XO Site.Node Site.xpt ChartInput.ηG_inl ChartInput.compG ChartInput.coe_support_compG ChartInput"
namespace ChartInput
p2m_export "V3Glue.ChartInput" "ηG_inl compG coe_support_compG xU vertex Y q a j j_q toGlueInput hq g toB toB_eq πX Res X0 U σ mk S one_le_thick B ρ x thick x_mem_U f mem_X0"
p2m_open "V3Glue.ChartInput V3Glue"

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

section strict

variable {S : Scheme.{0}} (ιS : S ⟶ C.toGlueInput.glued)
  (im : Set X) (ξ : X) (hξ : IsGenericPoint ξ im) (hξ0 : ξ ∈ C.X0)
  (hS : Set.range ιS.base = closure {C.toGlueInput.ιX0.base ⟨ξ, hξ0⟩})
  {F : N → Scheme.{0}} (lam : ∀ n, F n ⟶ C.Res n)
  (horient : ∀ n (y : C.U n), (C.f n).base y ∈ Set.range (lam n ≫ C.ρ n).base ↔ (y : X) ∈ im)
  (hxim : ∀ n, C.x n ∈ im)

include hξ hxim in
private theorem _root_.V3Glue.ChartInput.ξ_mem_U (n : N) : ξ ∈ C.U n :=
  (hξ.mem_open_set_iff (C.U n).2).mpr ⟨C.x n, hxim n, C.x_mem_U n⟩

p2m_export "V3Glue.ChartInput" "ξ_mem_U"

private def _root_.V3Glue.ChartInput.ηY (n : N) (hU : ξ ∈ C.U n) : C.Y n := (C.j n).base ⟨ξ, hU, hξ0⟩

p2m_export "V3Glue.ChartInput" "ηY"
private theorem _root_.V3Glue.ChartInput.ιY_ηY (n : N) (hU : ξ ∈ C.U n) :
    (C.toGlueInput.ιY n).base (C.ηY ξ hξ0 n hU) = C.toGlueInput.ιX0.base ⟨ξ, hξ0⟩ := by
  have h := congr($(C.toGlueInput.homOfLE_ιX0 n).base ⟨ξ, hU, hξ0⟩)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
  rw [ηY]
  refine h.symm.trans ?_
  congr 1
  apply Subtype.ext
  simpa using congr($(X.homOfLE_ι (inf_le_right : C.U n ⊓ C.X0 ≤ C.X0)).base ⟨ξ, hU, hξ0⟩)

p2m_export "V3Glue.ChartInput" "ιY_ηY"
private theorem _root_.V3Glue.ChartInput.q_ηY (n : N) (hU : ξ ∈ C.U n) : (C.q n).base (C.ηY ξ hξ0 n hU) = ⟨ξ, hU⟩ := by
  have h := congr($(C.j_q n).base ⟨ξ, hU, hξ0⟩)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
  rw [ηY, h]
  apply Subtype.ext
  simpa using congr($(X.homOfLE_ι (inf_le_left : C.U n ⊓ C.X0 ≤ C.U n)).base ⟨ξ, hU, hξ0⟩)

p2m_export "V3Glue.ChartInput" "q_ηY"

private theorem _root_.V3Glue.ChartInput.q_injOn_range_j (n : N) : Set.InjOn (C.q n).base (Set.range (C.j n).base) := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h
  have ha := congr($(C.j_q n).base a)
  have hb := congr($(C.j_q n).base b)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at ha hb
  rw [ha, hb] at h
  rw [(X.homOfLE (inf_le_left : C.U n ⊓ C.X0 ≤ C.U n)).isOpenEmbedding.injective h]

p2m_export "V3Glue.ChartInput" "q_injOn_range_j"

private scoped instance _root_.V3Glue.ChartInput.isClosedImmersion_G_q (n : N) [IsClosedImmersion (lam n ≫ C.ρ n)] :
    IsClosedImmersion (pullback.fst (C.g n) (lam n) ≫ C.q n) :=
  AlgebraicGeometry.isClosedImmersion_pullback_fst_snd_comp_fst (C.f n) (C.ρ n) (lam n)

p2m_export "V3Glue.ChartInput" "isClosedImmersion_G_q"
include horient in

private theorem _root_.V3Glue.ChartInput.range_G_q (n : N) :
    Set.range (pullback.fst (C.g n) (lam n) ≫ C.q n).base = {y : C.U n | (y : X) ∈ im} := by
  exact (AlgebraicGeometry.range_pullback_fst_snd_comp_fst (C.f n) (C.ρ n) (lam n)).trans
    (Set.ext fun y => horient n y)

p2m_export "V3Glue.ChartInput" "range_G_q"
include hξ horient hxim in

private theorem _root_.V3Glue.ChartInput.range_G (n : N) [IsClosedImmersion (lam n)] [IsClosedImmersion (lam n ≫ C.ρ n)] :
    Set.range (pullback.fst (C.g n) (lam n)).base = closure {C.ηY ξ hξ0 n (C.ξ_mem_U im ξ hξ hxim n)} := by
  have hU := C.ξ_mem_U im ξ hξ hxim n
  have hqη : (C.q n).base (C.ηY ξ hξ0 n hU) = ⟨ξ, hU⟩ := C.q_ηY ξ hξ0 n hU
  have hrange : Set.range (pullback.fst (C.g n) (lam n) ≫ C.q n).base = {y : C.U n | (y : X) ∈ im} :=
    C.range_G_q im lam horient n

  obtain ⟨z₀, hz₀⟩ : C.ηY ξ hξ0 n hU ∈ Set.range (pullback.fst (C.g n) (lam n)).base := by
    have h1 : (C.q n).base (C.ηY ξ hξ0 n hU) ∈ Set.range (pullback.fst (C.g n) (lam n) ≫ C.q n).base := by
      rw [hrange, hqη]; exact hξ.mem
    obtain ⟨z, hz⟩ := h1
    rw [Scheme.Hom.comp_base, TopCat.comp_app] at hz
    refine ⟨z, C.q_injOn_range_j n ?_ ⟨_, rfl⟩ hz⟩
    apply C.hq
    rw [hz, hqη]
    exact hξ0
  haveI : IsClosedImmersion (pullback.fst (C.g n) (lam n)) := MorphismProperty.pullback_fst (P := @IsClosedImmersion) _ _ inferInstance
  set h := pullback.fst (C.g n) (lam n) ≫ C.q n with hh
  have h3 : h.base z₀ = (C.q n).base (C.ηY ξ hξ0 n hU) := by
    rw [hh, Scheme.Hom.comp_base, TopCat.comp_app, hz₀]
  have hι3 : (C.U n).ι.base (h.base z₀) = ξ := by
    rw [h3, hqη]
    simp
  have hmem : ∀ w, (C.U n).ι.base (h.base w) ∈ im := fun w => by
    have hw : h.base w ∈ Set.range h.base := ⟨w, rfl⟩
    rw [hrange] at hw
    (first | exact hw | simpa using hw | (have h__ := hw; simp at h__; exact h__))
  have hindU : Topology.IsInducing (C.U n).ι.base := (C.U n).ι.isOpenEmbedding.isInducing
  have hindh : Topology.IsInducing h.base := h.isClosedEmbedding.isInducing
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    have hz' : z ∈ closure {z₀} := by
      rw [hindh.closure_eq_preimage_closure_image, Set.image_singleton, Set.mem_preimage,
        hindU.closure_eq_preimage_closure_image, Set.image_singleton, hι3, hξ.def, Set.mem_preimage]
      exact hmem z
    have h4 := image_closure_subset_closure_image (pullback.fst (C.g n) (lam n)).continuous ⟨z, hz', rfl⟩
    rwa [Set.image_singleton, hz₀] at h4
  · exact closure_minimal (Set.singleton_subset_iff.mpr ⟨z₀, hz₀⟩)
      (pullback.fst (C.g n) (lam n)).isClosedEmbedding.isClosed_range

p2m_export "V3Glue.ChartInput" "range_G"
include hξ horient hxim in

private theorem _root_.V3Glue.ChartInput.preimage_ιY_closure_eq_preimage_g_range (n : N) [IsClosedImmersion (lam n)] [IsClosedImmersion (lam n ≫ C.ρ n)] :
    (C.toGlueInput.ιY n).base ⁻¹' closure {C.toGlueInput.ιX0.base ⟨ξ, hξ0⟩} =
      (C.g n).base ⁻¹' Set.range (lam n).base := by
  rw [← Scheme.Pullback.range_fst, C.range_G im ξ hξ hξ0 lam horient hxim n,
    IsOpenMap.preimage_closure_eq_closure_preimage (C.toGlueInput.ιY n).isOpenEmbedding.isOpenMap
      (C.toGlueInput.ιY n).continuous]
  congr 1
  rw [← C.ιY_ηY ξ hξ0 n (C.ξ_mem_U im ξ hξ hxim n)]
  exact Set.ext fun y => (C.toGlueInput.ιY n).isOpenEmbedding.injective.eq_iff

p2m_export "V3Glue.ChartInput" "preimage_ιY_closure_eq_preimage_g_range"
end strict
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry"

end V3Glue.ChartInput
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.V3Glue P2MW.S_V3Asm_strict_iso_zero.V3Glue.ChartInput"
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.V3Glue"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective IsClosedImmersion.of_comp basicOpen_eq_bot_iff Scheme.Hom iSup_affineOpens_eq_top Scheme.Pullback.range_fst isPullback_morphismRestrict IsZariskiLocalAtTarget LocallyOfFiniteType Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme pullbackSpecIso IsOpenImmersion Spec.map_base Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced IsSeparated HasRingHomProperty.appLE SpecMap_ΓSpecIso_hom isAffineOpen_top Scheme.basicOpen_appLE Scheme.preimage_basicOpen_top Spec.map_id IsZariskiLocalAtTarget.of_iSup_eq_top Etale Scheme.Spec affine_isIntegral_iff FormallyUnramified isReduced_of_isOpenImmersion Scheme.Pullback.exists_preimage_pullback isReduced_of_isAffine_isReduced HasRingHomProperty Etale.iff_flat_and_formallyUnramified toSpecΓ basicOpen_eq_of_affine geometrically range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq"
p2m_open "AlgebraicGeometry"

theorem isClosedImmersion_morphismRestrict_of_isPullback {P S X : Scheme.{0}} {U : X.Opens} {ψ : S ⟶ X}
    {f' : P ⟶ U} {i : P ⟶ S} (sq : IsPullback f' i U.ι ψ) (hf' : IsClosedImmersion f') :
    IsClosedImmersion (ψ ∣_ U) := by
  have h := IsPullback.isoIsPullback_hom_fst (h := isPullback_morphismRestrict ψ U) (h' := sq)
  rw [← h]
  infer_instance

end AlgebraicGeometry
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.V3Glue P2MW.S_V3Asm_strict_iso_zero.V3Glue.ChartInput"

namespace V3Glue
p2m_export "V3Glue" "Site.XO Site.Node Site.xpt ChartInput.ηG_inl ChartInput.compG ChartInput.coe_support_compG ChartInput"
namespace ChartInput
p2m_export "V3Glue.ChartInput" "ηG_inl compG coe_support_compG xU vertex Y q a j j_q toGlueInput hq g toB toB_eq πX Res X0 U σ mk S one_le_thick B ρ x thick x_mem_U f mem_X0"
p2m_open "V3Glue.ChartInput V3Glue"

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)
  {S : Scheme.{0}} (ιS : S ⟶ C.toGlueInput.glued)
  (im : Set X) (ξ : X) (hξ : IsGenericPoint ξ im) (hξ0 : ξ ∈ C.X0)
  (hS : Set.range ιS.base = closure {C.toGlueInput.ιX0.base ⟨ξ, hξ0⟩})
  {F : N → Scheme.{0}} (lam : ∀ n, F n ⟶ C.Res n)
  (horient : ∀ n (y : C.U n), (C.f n).base y ∈ Set.range (lam n ≫ C.ρ n).base ↔ (y : X) ∈ im)
  (hxim : ∀ n, C.x n ∈ im)

include hξ hS horient hxim in

private theorem _root_.V3Glue.ChartInput.exists_iso_strictPiece (n : N) [IsClosedImmersion ιS] [IsReduced S] [IsClosedImmersion (lam n)]
    [IsClosedImmersion (lam n ≫ C.ρ n)] [IsReduced (pullback (C.g n) (lam n))] :
    ∃ e : pullback ιS (C.toGlueInput.ιY n) ≅ pullback (C.g n) (lam n),
      e.hom ≫ pullback.fst (C.g n) (lam n) = pullback.snd ιS (C.toGlueInput.ιY n) := by
  haveI : IsReduced (pullback ιS (C.toGlueInput.ιY n)) :=
    isReduced_of_isOpenImmersion (pullback.fst ιS (C.toGlueInput.ιY n))
  have hsnd : IsClosedImmersion (pullback.snd ιS (C.toGlueInput.ιY n)) :=
    MorphismProperty.pullback_snd (P := @IsClosedImmersion) _ _ inferInstance
  have hfst : IsClosedImmersion (pullback.fst (C.g n) (lam n)) :=
    MorphismProperty.pullback_fst (P := @IsClosedImmersion) _ _ inferInstance
  have hr : Set.range (pullback.snd ιS (C.toGlueInput.ιY n)).base =
      Set.range (pullback.fst (C.g n) (lam n)).base := by
    rw [Scheme.Pullback.range_snd, hS, Scheme.Pullback.range_fst]
    exact C.preimage_ιY_closure_eq_preimage_g_range im ξ hξ hξ0 lam horient hxim n
  exact @AlgebraicGeometry.IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq _ _ _
    (pullback.snd ιS (C.toGlueInput.ιY n)) (pullback.fst (C.g n) (lam n)) hsnd hfst inferInstance inferInstance hr

p2m_export "V3Glue.ChartInput" "exists_iso_strictPiece"
include hξ hS horient hxim in

private theorem _root_.V3Glue.ChartInput.isClosedImmersion_comp_toDR [IsClosedImmersion ιS] [IsReduced S] [∀ n, IsClosedImmersion (lam n)]
    [∀ n, IsClosedImmersion (lam n ≫ C.ρ n)] [∀ n, IsReduced (pullback (C.g n) (lam n))] :
    IsClosedImmersion (ιS ≫ C.toGlueInput.toDR) := by
  let Uc : Option N → X.Opens := fun i => i.elim C.X0 C.U
  have hU : ⨆ i, Uc i = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    by_cases hx : ∀ n, x ≠ C.x n
    · exact Opens.mem_iSup.mpr ⟨none, (C.mem_X0 x).mpr hx⟩
    · push Not at hx
      obtain ⟨n, rfl⟩ := hx
      exact Opens.mem_iSup.mpr ⟨some n, C.x_mem_U n⟩
  apply IsZariskiLocalAtTarget.of_iSup_eq_top Uc hU
  rintro (_ | n)
  ·
    change IsClosedImmersion ((ιS ≫ C.toGlueInput.toDR) ∣_ C.X0)
    have sq : IsPullback (pullback.snd ιS C.toGlueInput.ιX0 ≫ 𝟙 _) (pullback.fst ιS C.toGlueInput.ιX0)
        C.X0.ι (ιS ≫ C.toGlueInput.toDR) :=
      (IsPullback.of_hasPullback ιS C.toGlueInput.ιX0).flip.paste_horiz (C.toGlueInput.isPullback_ιX0 C.hq)
    rw [Category.comp_id] at sq
    have hsnd : IsClosedImmersion (pullback.snd ιS C.toGlueInput.ιX0) :=
      MorphismProperty.pullback_snd (P := @IsClosedImmersion) _ _ inferInstance
    exact AlgebraicGeometry.isClosedImmersion_morphismRestrict_of_isPullback sq hsnd
  ·
    change IsClosedImmersion ((ιS ≫ C.toGlueInput.toDR) ∣_ C.U n)
    have sq : IsPullback (pullback.snd ιS (C.toGlueInput.ιY n) ≫ C.q n) (pullback.fst ιS (C.toGlueInput.ιY n))
        (C.U n).ι (ιS ≫ C.toGlueInput.toDR) :=
      (IsPullback.of_hasPullback ιS (C.toGlueInput.ιY n)).flip.paste_horiz (C.toGlueInput.isPullback_ιY C.hq n)
    obtain ⟨e, he⟩ := C.exists_iso_strictPiece ιS im ξ hξ hξ0 hS lam horient hxim n
    have hE : pullback.snd ιS (C.toGlueInput.ιY n) ≫ C.q n =
        e.hom ≫ (pullback.fst (C.g n) (lam n) ≫ C.q n) := by
      rw [← he]; exact Category.assoc _ _ _
    have hcomp : IsClosedImmersion (pullback.snd ιS (C.toGlueInput.ιY n) ≫ C.q n) := by
      rw [hE]
      exact (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion e.hom _).mpr
        (C.isClosedImmersion_G_q lam n)
    exact AlgebraicGeometry.isClosedImmersion_morphismRestrict_of_isPullback sq hcomp

p2m_export "V3Glue.ChartInput" "isClosedImmersion_comp_toDR"
include hξ hS in

private theorem _root_.V3Glue.ChartInput.range_comp_toDR [IsClosedImmersion (ιS ≫ C.toGlueInput.toDR)] :
    Set.range (ιS ≫ C.toGlueInput.toDR).base = im := by
  have hx0 : C.toGlueInput.toDR.base (C.toGlueInput.ιX0.base ⟨ξ, hξ0⟩) = ξ := by
    have h := congr($(C.toGlueInput.ιX0_toDR).base ⟨ξ, hξ0⟩)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    rw [h]
    simp
  apply le_antisymm
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hS, ← hξ.def]
    refine (image_closure_subset_closure_image C.toGlueInput.toDR.continuous).trans ?_
    rw [Set.image_singleton, hx0]
  · rw [← hξ.def]
    refine closure_minimal ?_ (ιS ≫ C.toGlueInput.toDR).isClosedEmbedding.isClosed_range
    rw [Set.singleton_subset_iff]
    have hη : C.toGlueInput.ιX0.base ⟨ξ, hξ0⟩ ∈ Set.range ιS.base := by
      rw [hS]; exact subset_closure rfl
    obtain ⟨s, hs⟩ := hη
    exact ⟨s, by rw [Scheme.Hom.comp_base, TopCat.comp_app, hs, hx0]⟩

p2m_export "V3Glue.ChartInput" "range_comp_toDR"
include hξ hS horient hxim in

private theorem _root_.V3Glue.ChartInput.isReduced_pullback_strict [IsClosedImmersion ιS] [IsIntegral S] [∀ n, IsClosedImmersion (lam n)]
    [∀ n, IsClosedImmersion (lam n ≫ C.ρ n)] [∀ n, IsReduced (pullback (C.g n) (lam n))]
    (n₀ : N) {Bκ B₀ : Scheme.{0}} (i : B₀ ⟶ C.B) [Mono i] (a : Bκ ⟶ B₀) [Flat a] (s₀ : S ⟶ B₀)
    (hsB : ιS ≫ C.toGlueInput.toDR ≫ C.πX = s₀ ≫ i)
    (sB : S ⟶ C.B) (b : Bκ ⟶ C.B) (hs : sB = s₀ ≫ i) (hb : b = a ≫ i)
    (hGκ : IsReduced (pullback (pullback.fst (C.g n₀) (lam n₀) ≫ C.toB n₀) b)) :
    IsReduced (pullback sB b) := by
  subst hs hb
  haveI : Flat (pullback.fst (s₀ ≫ i) (a ≫ i)) := AlgebraicGeometry.flat_pullback_fst_comp_mono s₀ a i

  have hU := C.ξ_mem_U im ξ hξ hxim n₀
  have hV : ((pullback.fst ιS (C.toGlueInput.ιY n₀)).opensRange : Set S).Nonempty := by
    have hη : C.toGlueInput.ιX0.base ⟨ξ, hξ0⟩ ∈ Set.range ιS.base := by
      rw [hS]; exact subset_closure rfl
    obtain ⟨s, hs⟩ := hη
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := ιS) (g := C.toGlueInput.ιY n₀)
      s (C.ηY ξ hξ0 n₀ hU) (hs.trans (C.ιY_ηY ξ hξ0 n₀ hU).symm)
    exact ⟨(pullback.fst ιS (C.toGlueInput.ιY n₀)).base w, ⟨w, rfl⟩⟩

  obtain ⟨e, he⟩ := C.exists_iso_strictPiece ιS im ξ hξ hξ0 hS lam horient hxim n₀
  have h2' : C.q n₀ ≫ (C.U n₀).ι = C.toGlueInput.ιY n₀ ≫ C.toGlueInput.toDR := (C.toGlueInput.ιY_toDR n₀).symm
  have hcond : pullback.fst ιS (C.toGlueInput.ιY n₀) ≫ ιS =
      pullback.snd ιS (C.toGlueInput.ιY n₀) ≫ C.toGlueInput.ιY n₀ := pullback.condition
  have E1 : pullback.fst ιS (C.toGlueInput.ιY n₀) ≫ s₀ ≫ i =
      (pullback.fst ιS (C.toGlueInput.ιY n₀) ≫ ιS) ≫ (C.toGlueInput.toDR ≫ C.πX) := by
    rw [← hsB]; exact (Category.assoc _ _ _).symm
  have E2 : (pullback.fst ιS (C.toGlueInput.ιY n₀) ≫ ιS) ≫ (C.toGlueInput.toDR ≫ C.πX) =
      (pullback.snd ιS (C.toGlueInput.ιY n₀) ≫ C.toGlueInput.ιY n₀) ≫ (C.toGlueInput.toDR ≫ C.πX) := by
    rw [hcond]
  have E3 : (pullback.snd ιS (C.toGlueInput.ιY n₀) ≫ C.toGlueInput.ιY n₀) ≫ (C.toGlueInput.toDR ≫ C.πX) =
      pullback.snd ιS (C.toGlueInput.ιY n₀) ≫ ((C.toGlueInput.ιY n₀ ≫ C.toGlueInput.toDR) ≫ C.πX) := by
    simp only [Category.assoc]
  have E4 : pullback.snd ιS (C.toGlueInput.ιY n₀) ≫ ((C.toGlueInput.ιY n₀ ≫ C.toGlueInput.toDR) ≫ C.πX) =
      pullback.snd ιS (C.toGlueInput.ιY n₀) ≫ ((C.q n₀ ≫ (C.U n₀).ι) ≫ C.πX) :=
    congrArg (fun k => pullback.snd ιS (C.toGlueInput.ιY n₀) ≫ k ≫ C.πX) h2'.symm
  have E5 : pullback.snd ιS (C.toGlueInput.ιY n₀) ≫ ((C.q n₀ ≫ (C.U n₀).ι) ≫ C.πX) =
      pullback.snd ιS (C.toGlueInput.ιY n₀) ≫ C.toB n₀ := by
    rw [C.toB_eq]; congr 1
  have E6 : pullback.snd ιS (C.toGlueInput.ιY n₀) ≫ C.toB n₀ =
      (e.hom ≫ pullback.fst (C.g n₀) (lam n₀)) ≫ C.toB n₀ :=
    congrArg (· ≫ C.toB n₀) he.symm
  have hcomm : pullback.fst ιS (C.toGlueInput.ιY n₀) ≫ s₀ ≫ i =
      (e.hom ≫ pullback.fst (C.g n₀) (lam n₀)) ≫ C.toB n₀ :=
    E1.trans (E2.trans (E3.trans (E4.trans (E5.trans E6))))
  haveI : IsReduced (pullback e.hom (pullback.fst (pullback.fst (C.g n₀) (lam n₀) ≫ C.toB n₀) (a ≫ i))) :=
    isReduced_of_isOpenImmersion
      (pullback.snd e.hom (pullback.fst (pullback.fst (C.g n₀) (lam n₀) ≫ C.toB n₀) (a ≫ i)))
  haveI : IsReduced (pullback (e.hom ≫ pullback.fst (C.g n₀) (lam n₀) ≫ C.toB n₀) (a ≫ i)) :=
    isReduced_of_isOpenImmersion
      (pullbackRightPullbackFstIso (pullback.fst (C.g n₀) (lam n₀) ≫ C.toB n₀) (a ≫ i) e.hom).inv
  haveI : IsReduced (pullback (pullback.fst ιS (C.toGlueInput.ιY n₀)) (pullback.fst (s₀ ≫ i) (a ≫ i))) :=
    isReduced_of_isOpenImmersion
      ((pullbackRightPullbackFstIso (s₀ ≫ i) (a ≫ i) (pullback.fst ιS (C.toGlueInput.ιY n₀))).hom ≫
        (pullback.congrHom hcomm rfl).hom ≫ (pullback.congrHom (Category.assoc _ _ _) rfl).hom)
  exact AlgebraicGeometry.isReduced_of_flat_of_isReduced_preimage (pullback.fst (s₀ ≫ i) (a ≫ i))
    (pullback.fst ιS (C.toGlueInput.ιY n₀)).opensRange hV
    (pullback.snd (pullback.fst ιS (C.toGlueInput.ιY n₀)) (pullback.fst (s₀ ≫ i) (a ≫ i)))
    (fun x hx => by
      show x ∈ Set.range (pullback.snd (pullback.fst ιS (C.toGlueInput.ιY n₀)) (pullback.fst (s₀ ≫ i) (a ≫ i))).base
      rw [Scheme.Pullback.range_snd]
      exact hx)

p2m_export "V3Glue.ChartInput" "isReduced_pullback_strict"
end V3Glue.ChartInput
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.V3Glue P2MW.S_V3Asm_strict_iso_zero.V3Glue.ChartInput"
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.V3Glue P2MW.S_V3Asm_strict_iso_zero.V3Glue.ChartInput"

end
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.V3Glue P2MW.S_V3Asm_strict_iso_zero.V3Glue.ChartInput"

p2m_open "AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry CategoryTheory TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective IsClosedImmersion.of_comp basicOpen_eq_bot_iff Scheme.Hom iSup_affineOpens_eq_top Scheme.Pullback.range_fst isPullback_morphismRestrict IsZariskiLocalAtTarget LocallyOfFiniteType Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme pullbackSpecIso IsOpenImmersion Spec.map_base Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced IsSeparated HasRingHomProperty.appLE SpecMap_ΓSpecIso_hom isAffineOpen_top Scheme.basicOpen_appLE Scheme.preimage_basicOpen_top Spec.map_id IsZariskiLocalAtTarget.of_iSup_eq_top Etale Scheme.Spec affine_isIntegral_iff FormallyUnramified isReduced_of_isOpenImmersion Scheme.Pullback.exists_preimage_pullback isReduced_of_isAffine_isReduced HasRingHomProperty Etale.iff_flat_and_formallyUnramified toSpecΓ basicOpen_eq_of_affine geometrically range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "mem_basicOpen Hom mk Γ empty Pullback.range_fst topIso IdealSheafData.range_subschemeι toSpecΓ_naturality basicOpen_zero Hom.comp_base zeroLocus Pullback.range_snd affineOpens basicOpen basicOpen_appLE preimage_basicOpen_top openCoverOfIsOpenCover isBasis_affineOpens Opens residue homOfLE_ι Pullback.exists_preimage_pullback IdealSheafData ΓSpecIso toSpecΓ"
namespace IdealSheafData
p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "radical coe_support_vanishingIdeal mk map subscheme range_subschemeι map_id vanishingIdeal vanishingIdeal_ideal ideal map_comp subschemeι comap subschemeCover support"
p2m_open "AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}}

theorem isReduced_Spec_of_isReduced (R : Type u) [CommRing R] [_root_.IsReduced R] :
    IsReduced (Spec (CommRingCat.of R)) := by
  haveI : _root_.IsReduced Γ(Spec (CommRingCat.of R), ⊤) :=
    isReduced_of_injective (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isAffine_isReduced _

theorem isReduced_subscheme_of_isRadical (I : X.IdealSheafData)
    (hI : ∀ U : X.affineOpens, (I.ideal U).IsRadical) : IsReduced I.subscheme := by
  haveI : ∀ i, IsReduced (I.subschemeCover.openCover.X i) := fun (U : X.affineOpens) => by
    change IsReduced (Spec (CommRingCat.of (Γ(X, (U : X.Opens)) ⧸ I.ideal U)))
    haveI : _root_.IsReduced (Γ(X, (U : X.Opens)) ⧸ I.ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp (hI U)
    exact isReduced_Spec_of_isReduced _
  exact IsReduced.of_openCover _ I.subschemeCover.openCover

scoped instance isReduced_subscheme_vanishingIdeal (Z : Closeds X) : IsReduced (vanishingIdeal Z).subscheme :=
  isReduced_subscheme_of_isRadical _ fun U => by
    rw [vanishingIdeal_ideal]
    exact PrimeSpectrum.isRadical_vanishingIdeal _

theorem isIntegral_subscheme_vanishingIdeal_closure_singleton (x : X) :
    IsIntegral (vanishingIdeal ⟨closure {x}, isClosed_closure⟩).subscheme := by
  set I : X.IdealSheafData := vanishingIdeal ⟨closure {x}, isClosed_closure⟩
  have hsupp : (I.support : Set X) = closure {x} := by
    rw [coe_support_vanishingIdeal]; rfl

  have hx : x ∈ Set.range I.subschemeι.base := by
    rw [range_subschemeι, hsupp]; exact subset_closure rfl
  obtain ⟨s, hs⟩ := hx

  have hind : Topology.IsInducing I.subschemeι.base := I.subschemeι.isClosedEmbedding.isInducing
  have hgen : closure ({s} : Set I.subscheme) = Set.univ := by
    rw [hind.closure_eq_preimage_closure_image, Set.image_singleton, hs, ← hsupp, ← range_subschemeι,
      Set.preimage_range]
  haveI : IrreducibleSpace I.subscheme := by
    rw [irreducibleSpace_def, Set.top_eq_univ, ← hgen]
    exact isIrreducible_singleton.closure
  exact (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme.IdealSheafData
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.V3Glue P2MW.S_V3Asm_strict_iso_zero.V3Glue.ChartInput P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme.IdealSheafData"
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.V3Glue P2MW.S_V3Asm_strict_iso_zero.V3Glue.ChartInput P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.V3Glue P2MW.S_V3Asm_strict_iso_zero.V3Glue.ChartInput"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective IsClosedImmersion.of_comp basicOpen_eq_bot_iff Scheme.Hom iSup_affineOpens_eq_top Scheme.Pullback.range_fst isPullback_morphismRestrict IsZariskiLocalAtTarget LocallyOfFiniteType Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme pullbackSpecIso IsOpenImmersion Spec.map_base Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced IsSeparated HasRingHomProperty.appLE SpecMap_ΓSpecIso_hom isAffineOpen_top Scheme.basicOpen_appLE Scheme.preimage_basicOpen_top Spec.map_id IsZariskiLocalAtTarget.of_iSup_eq_top Etale Scheme.Spec affine_isIntegral_iff FormallyUnramified isReduced_of_isOpenImmersion Scheme.Pullback.exists_preimage_pullback isReduced_of_isAffine_isReduced HasRingHomProperty Etale.iff_flat_and_formallyUnramified toSpecΓ basicOpen_eq_of_affine geometrically range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq"
p2m_open "AlgebraicGeometry"

theorem isGenericPoint_image_genericPoint {R X : Scheme.{u}} [IsIntegral R] (h : R ⟶ X) :
    IsGenericPoint (h.base (genericPoint R)) (closure (Set.range h.base)) := by
  have := (genericPoint_spec R).image h.continuous
  rwa [Set.image_univ] at this

theorem range_specMap_of_ker_eq_maximalIdeal {O κ : Type u} [CommRing O] [IsLocalRing O] [Field κ]
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

theorem IsPullback.range_fst' {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) : Set.range fst.base = f.base ⁻¹' Set.range g.base := by
  have hsurj : Function.Surjective h.isoPullback.hom.base := h.isoPullback.hom.homeomorph.surjective
  rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr hsurj, Set.image_univ, Scheme.Pullback.range_fst]

theorem iff_mem_closure_of_orientation {R Xκ X : Scheme.{u}} (c : R ⟶ Xκ) (bcm : Xκ ⟶ X) {U : X.Opens}
    (P : U → Prop)
    (hfwd : ∀ y : U, P y → (y : X) ∈ Set.range (c ≫ bcm).base)
    (hconv : ∀ y : U, (y : X) ∈ Set.range (c ≫ bcm).base → P y)
    (hdesc : bcm.base ⁻¹' closure (bcm.base '' Set.range c.base) = Set.range c.base)
    (hfib : closure (Set.range (c ≫ bcm).base) ⊆ Set.range bcm.base) (y : U) :
    P y ↔ (y : X) ∈ closure (Set.range (c ≫ bcm).base) := by
  have him : Set.range (c ≫ bcm).base = bcm.base '' Set.range c.base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  constructor
  · exact fun h => subset_closure (hfwd y h)
  · intro h
    apply hconv
    obtain ⟨r, hr⟩ := hfib h
    rw [him] at h ⊢
    have hr' : r ∈ bcm.base ⁻¹' closure (bcm.base '' Set.range c.base) := by
      rw [Set.mem_preimage, hr]; exact h
    rw [hdesc] at hr'
    exact ⟨r, hr', hr⟩

theorem closure_subset_preimage_singleton {X B : Scheme.{u}} (π : X ⟶ B) {s : Set X} {b : B}
    (hb : IsClosed ({b} : Set B)) (hs : s ⊆ π.base ⁻¹' {b}) : closure s ⊆ π.base ⁻¹' {b} :=
  closure_minimal hs (hb.preimage π.continuous)

theorem preimage_basicOpen_eq_bot_of_forall_eq_closedPoint {S : Scheme.{u}} {O : Type u} [CommRing O] [IsLocalRing O]
    (f : S ⟶ Spec (CommRingCat.of O)) (hf : ∀ s : S, f.base s = IsLocalRing.closedPoint O) (r : O)
    (hr : r ∈ IsLocalRing.maximalIdeal O) :
    f ⁻¹ᵁ (PrimeSpectrum.basicOpen r : (Spec (CommRingCat.of O)).Opens) = ⊥ := by
  ext s
  simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro hs
  have hs' : f.base s ∈ PrimeSpectrum.basicOpen r := hs
  rw [hf s] at hs'
  exact (PrimeSpectrum.mem_basicOpen _ _).mp hs' hr

theorem forall_comp_eq_of_range_eq_closure {S Y B : Scheme.{u}} (ιS : S ⟶ Y) (g : Y ⟶ B) {y : Y} {b : B}
    (hS : Set.range ιS.base = closure {y}) (hy : g.base y = b) (hb : IsClosed ({b} : Set B)) (s : S) :
    (ιS ≫ g).base s = b := by
  have h1 : closure {y} ⊆ g.base ⁻¹' {b} :=
    closure_subset_preimage_singleton g hb (by rintro _ rfl; exact hy)
  have h2 : ιS.base s ∈ closure {y} := by rw [← hS]; exact ⟨s, rfl⟩
  exact h1 h2

end AlgebraicGeometry
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.V3Glue P2MW.S_V3Asm_strict_iso_zero.V3Glue.ChartInput P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme.IdealSheafData"

noncomputable section

namespace V3Glue
p2m_export "V3Glue" "Site.XO Site.Node Site.xpt ChartInput.ηG_inl ChartInput.compG ChartInput.coe_support_compG ChartInput"
namespace ChartInput
p2m_export "V3Glue.ChartInput" "ηG_inl compG coe_support_compG xU vertex Y q a j j_q toGlueInput hq g toB toB_eq πX Res X0 U σ mk S one_le_thick B ρ x thick x_mem_U f mem_X0"
p2m_open "V3Glue.ChartInput V3Glue"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry TopologicalSpace"

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

private theorem _root_.V3Glue.ChartInput.strict_iso_of
    (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
    (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
    (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0) (j : Fin 2)

    {R Xκ Bκ : Scheme.{0}} (c : R ⟶ Xκ) [IsClosedImmersion c] [IsIntegral R]
    (bcm : Xκ ⟶ X) (p₂ : Xκ ⟶ Bκ) (b : Bκ ⟶ C.B) (hP : IsPullback bcm p₂ C.πX b)
    (hξj : ξ j = (c ≫ bcm).base (genericPoint R))
    (hdesc : bcm.base ⁻¹' closure (bcm.base '' Set.range c.base) = Set.range c.base)
    {pt : C.B} (hpt : IsClosed ({pt} : Set C.B)) (hfib : Set.range bcm.base = C.πX.base ⁻¹' {pt})
    (hcpt : ∀ r : R, (c ≫ bcm ≫ C.πX).base r = pt)

    {F : N → Scheme.{0}} (lam : ∀ n, F n ⟶ C.Res n) [∀ n, IsClosedImmersion (lam n)]
    [∀ n, IsClosedImmersion (lam n ≫ C.ρ n)] [∀ n, IsReduced (pullback (C.g n) (lam n))]
    (horient_fwd : ∀ n (y : C.U n), (C.f n).base y ∈ Set.range (lam n ≫ C.ρ n).base →
      (y : X) ∈ Set.range (c ≫ bcm).base)
    (horient_conv : ∀ n (y : C.U n), (y : X) ∈ Set.range (c ≫ bcm).base →
      (C.f n).base y ∈ Set.range (lam n ≫ C.ρ n).base)
    (hxim : ∀ n, C.x n ∈ Set.range (c ≫ bcm).base)

    (n₀ : N) {B₀ : Scheme.{0}} (i : B₀ ⟶ C.B) [Mono i] (a : Bκ ⟶ B₀) [Flat a] (hb : b = a ≫ i)
    (s₀ : (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subscheme ⟶ B₀)
    (hsB : (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι ≫ C.toGlueInput.toDR ≫ C.πX = s₀ ≫ i)
    (hGκ : IsReduced (pullback (pullback.fst (C.g n₀) (lam n₀) ≫ C.toB n₀) b)) :
    ∃ e : pullback ((C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι ≫ C.toGlueInput.toDR ≫ C.πX) b ⟶ R,
      IsIso e ∧ e ≫ c ≫ p₂ = pullback.snd _ _ ∧
        e ≫ c ≫ bcm = pullback.fst _ _ ≫ (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι ≫ C.toGlueInput.toDR := by

  set im : Set X := closure (Set.range (c ≫ bcm).base) with him
  have hgen : IsGenericPoint (ξ j) im := by
    rw [hξj]; exact AlgebraicGeometry.isGenericPoint_image_genericPoint (c ≫ bcm)
  have hS : Set.range (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι.base = closure {C.toGlueInput.ιX0.base ⟨ξ j, hξ j⟩} := by
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_compG, ηG_inl]
  have horient : ∀ n (y : C.U n), (C.f n).base y ∈ Set.range (lam n ≫ C.ρ n).base ↔ (y : X) ∈ im := by
    intro n y
    refine AlgebraicGeometry.iff_mem_closure_of_orientation c bcm
      (fun y : C.U n => (C.f n).base y ∈ Set.range (lam n ≫ C.ρ n).base) (horient_fwd n) (horient_conv n) hdesc ?_ y
    rw [hfib]
    refine AlgebraicGeometry.closure_subset_preimage_singleton C.πX hpt ?_
    rintro _ ⟨r, rfl⟩
    exact hcpt r
  have hxim' : ∀ n, C.x n ∈ im := fun n => subset_closure (hxim n)

  haveI : IsIntegral (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure_singleton _

  haveI hG1 : IsClosedImmersion ((C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι ≫ C.toGlueInput.toDR) :=
    C.isClosedImmersion_comp_toDR (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι im (ξ j) hgen (hξ j) hS lam horient hxim'

  have hG2 : bcm.base ⁻¹' Set.range ((C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι ≫ C.toGlueInput.toDR).base = Set.range c.base := by
    rw [C.range_comp_toDR (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι im (ξ j) hgen (hξ j) hS, him, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.range_comp]
    exact hdesc

  haveI hG3 : IsReduced (pullback ((C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι ≫ C.toGlueInput.toDR ≫ C.πX) b) :=
    C.isReduced_pullback_strict (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι im (ξ j) hgen (hξ j) hS lam horient hxim' n₀ i a s₀ hsB _ b hsB hb hGκ

  exact AlgebraicGeometry.exists_iso_pullback_of_isClosedImmersion_of_preimage_range_eq (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι
    C.toGlueInput.toDR C.πX (C.toGlueInput.toDR ≫ C.πX) rfl b bcm p₂ hP c hG2

p2m_export "V3Glue.ChartInput" "strict_iso_of"
end V3Glue.ChartInput
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.V3Glue P2MW.S_V3Asm_strict_iso_zero.V3Glue.ChartInput P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme.IdealSheafData"
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.V3Glue P2MW.S_V3Asm_strict_iso_zero.V3Glue.ChartInput P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme.IdealSheafData"

end
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.V3Glue P2MW.S_V3Asm_strict_iso_zero.V3Glue.ChartInput P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme.IdealSheafData"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry TopologicalSpace"

namespace Algebra
p2m_export "Algebra" "EssFiniteType trace commutes FormallyUnramified.of_restrictScalars mk algebraMap FormallyUnramified eq_top_iff algebraMapSubmonoid TensorProduct.comm FiniteType Etale smul_def EssFiniteType.of_comp id coe_bot FormallyUnramified.isReduced_of_field"
p2m_open "Algebra"

theorem mem_nonZeroDivisors_algebraMap_of_flat (D B : Type*) [CommRing D] [CommRing B] [Algebra D B]
    [Module.Flat D B] {r : D} (hr : r ∈ nonZeroDivisors D) : algebraMap D B r ∈ nonZeroDivisors B := by
  have hsm : IsSMulRegular B r := Module.Flat.isSMulRegular_of_nonZeroDivisors hr
  have key : ∀ x : B, algebraMap D B r * x = 0 → x = 0 := fun x hx =>
    hsm ((Algebra.smul_def r x).trans (hx.trans (smul_zero r).symm))
  exact mem_nonZeroDivisors_iff.mpr ⟨key, fun x hx => key x ((mul_comm _ _).trans hx)⟩

theorem isReduced_of_flat_of_formallyUnramified_of_isDomain (D B : Type*) [CommRing D] [IsDomain D]
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
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.V3Glue P2MW.S_V3Asm_strict_iso_zero.V3Glue.ChartInput P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme.IdealSheafData"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective IsClosedImmersion.of_comp basicOpen_eq_bot_iff Scheme.Hom iSup_affineOpens_eq_top Scheme.Pullback.range_fst isPullback_morphismRestrict IsZariskiLocalAtTarget LocallyOfFiniteType Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme pullbackSpecIso IsOpenImmersion Spec.map_base Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced IsSeparated HasRingHomProperty.appLE SpecMap_ΓSpecIso_hom isAffineOpen_top Scheme.basicOpen_appLE Scheme.preimage_basicOpen_top Spec.map_id IsZariskiLocalAtTarget.of_iSup_eq_top Etale Scheme.Spec affine_isIntegral_iff FormallyUnramified isReduced_of_isOpenImmersion Scheme.Pullback.exists_preimage_pullback isReduced_of_isAffine_isReduced HasRingHomProperty Etale.iff_flat_and_formallyUnramified toSpecΓ basicOpen_eq_of_affine geometrically range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq"
p2m_open "AlgebraicGeometry"

theorem isReduced_of_affineOpens (X : Scheme.{u}) (h : ∀ V : X.affineOpens, _root_.IsReduced Γ(X, V)) :
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

theorem isReduced_of_flat_of_formallyUnramified {D : Type u} [CommRing D] [IsDomain D] {X : Scheme.{u}}
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

theorem isReduced_of_etale {D : Type u} [CommRing D] [IsDomain D] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of D)) [Etale f] : IsReduced X := by
  haveI : Flat f := (Etale.iff_flat_and_formallyUnramified.mp inferInstance).1
  haveI : LocallyOfFiniteType f := inferInstance
  exact isReduced_of_flat_of_formallyUnramified f

end AlgebraicGeometry
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.V3Glue P2MW.S_V3Asm_strict_iso_zero.V3Glue.ChartInput P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme.IdealSheafData"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective IsClosedImmersion.of_comp basicOpen_eq_bot_iff Scheme.Hom iSup_affineOpens_eq_top Scheme.Pullback.range_fst isPullback_morphismRestrict IsZariskiLocalAtTarget LocallyOfFiniteType Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme pullbackSpecIso IsOpenImmersion Spec.map_base Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced IsSeparated HasRingHomProperty.appLE SpecMap_ΓSpecIso_hom isAffineOpen_top Scheme.basicOpen_appLE Scheme.preimage_basicOpen_top Spec.map_id IsZariskiLocalAtTarget.of_iSup_eq_top Etale Scheme.Spec affine_isIntegral_iff FormallyUnramified isReduced_of_isOpenImmersion Scheme.Pullback.exists_preimage_pullback isReduced_of_isAffine_isReduced HasRingHomProperty Etale.iff_flat_and_formallyUnramified toSpecΓ basicOpen_eq_of_affine geometrically range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq"
p2m_open "AlgebraicGeometry"

open _root_.AlgebraicGeometry.Polynomial in

theorem isDomain_polynomial_tensor (k₀ κ : Type u) [Field k₀] [Field κ] [Algebra k₀ κ] :
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

theorem isReduced_pullback_of_etale_over_line
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
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.V3Glue P2MW.S_V3Asm_strict_iso_zero.V3Glue.ChartInput P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme.IdealSheafData"

noncomputable section

namespace MvPolynomial
p2m_export "MvPolynomial" "X map R zeroLocus ext support algebraMap_apply ringHom_ext comap vanishingIdeal algebraMap_eq C algHom_ext' algHom_ext map_id CrossingQuotient.Resolution CrossingQuotient.U CrossingQuotient.V CrossingQuotient CrossingQuotient.exists_algEquiv_quotient_span_U_and_span_V_polynomial"
namespace CrossingQuotient
p2m_export "MvPolynomial.CrossingQuotient" "crossingScheme Resolution Resolution.ι Resolution.toCrossing Resolution.toSpec U V U_mul_V lift lift_U lift_V resolutionChart resolutionChart_U resolutionChart_V mk mk_surjective Resolution.isSeparated exists_algEquiv_quotient_span_U_and_span_V_polynomial"
namespace Resolution
p2m_export "MvPolynomial.CrossingQuotient.Resolution" "ι openCover toCrossing ι_toCrossing toSpec ι_toSpec hom_ext isSeparated"
p2m_open "MvPolynomial.CrossingQuotient.Resolution MvPolynomial.CrossingQuotient MvPolynomial"

p2m_open "AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial AlgebraicGeometry.Polynomial"

universe w

variable {W : Type w} [CommRing W] (t : W)

def lineVAlgHom : W ⧸ Ideal.span {t} →+* CrossingQuotient W t ⧸ Ideal.span {V t} :=
  Ideal.Quotient.lift (Ideal.span {t}) (algebraMap W _) (fun a ha => by
    rw [Ideal.mem_span_singleton'] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [IsScalarTower.algebraMap_apply W (CrossingQuotient W t) (_ ⧸ _), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact Ideal.mul_mem_left _ _ (algebraMap_mem_span_V' t))

theorem lineVAlgHom_comp_mk : (lineVAlgHom t).comp (Ideal.Quotient.mk _) = algebraMap W _ :=
  Ideal.Quotient.lift_comp_mk _ _ _

theorem exists_iso_spec_lineV :
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

theorem isIntegral_spec_lineV [IsDomain (W ⧸ Ideal.span {t})] :
    IsIntegral (Spec (CommRingCat.of (CrossingQuotient W t ⧸ Ideal.span {V t}))) := by
  obtain ⟨-, E, -⟩ := MvPolynomial.CrossingQuotient.exists_algEquiv_quotient_span_U_and_span_V_polynomial t
  haveI : IsDomain (CrossingQuotient W t ⧸ Ideal.span {V t}) :=
    MulEquiv.isDomain (Polynomial (W ⧸ Ideal.span {t})) E.toMulEquiv
  exact (affine_isIntegral_iff _).mpr ‹_›

section chartPiece

variable (e : ℕ) (he : 0 < e) {Uc : Scheme.{w}} (f : Uc ⟶ crossingScheme (t ^ e)) [Etale f]

theorem isReduced_chartPiece_strictV [IsDomain (W ⧸ Ideal.span {t})] :
    IsReduced (pullback (pullback.snd f (toCrossing t e)) (strictVι t e he)) := by
  obtain ⟨eF, -⟩ := exists_iso_spec_lineV t
  haveI : IsDomain (Polynomial (W ⧸ Ideal.span {t})) := inferInstance
  haveI : Etale (pullback.snd (pullback.snd f (toCrossing t e)) (strictVι t e he) ≫ eF.hom) := inferInstance
  exact isReduced_of_etale (pullback.snd (pullback.snd f (toCrossing t e)) (strictVι t e he) ≫ eF.hom)

theorem strictVι_toSpec :
    strictVι t e he ≫ toSpec t e = Spec.map (CommRingCat.ofHom (algebraMap W (CrossingQuotient W t ⧸ Ideal.span {V t}))) := by
  rw [strictVι, Category.assoc, ι_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

variable (hmax : (Ideal.span {t}).IsMaximal) {κ : Type w} [Field κ] (toκ : W →+* κ) (htoκ : toκ t = 0)

include hmax htoκ in

theorem isReduced_pullback_chartPiece_strictV_fibre :
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
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.V3Glue P2MW.S_V3Asm_strict_iso_zero.V3Glue.ChartInput P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme.IdealSheafData"

def lineUAlgHom : W ⧸ Ideal.span {t} →+* CrossingQuotient W t ⧸ Ideal.span {U t} :=
  Ideal.Quotient.lift (Ideal.span {t}) (algebraMap W _) (fun a ha => by
    rw [Ideal.mem_span_singleton'] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [IsScalarTower.algebraMap_apply W (CrossingQuotient W t) (_ ⧸ _), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact Ideal.mul_mem_left _ _ (algebraMap_mem_span_U' t))

theorem lineUAlgHom_comp_mk : (lineUAlgHom t).comp (Ideal.Quotient.mk _) = algebraMap W _ :=
  Ideal.Quotient.lift_comp_mk _ _ _

theorem exists_iso_spec_lineU :
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

theorem isIntegral_spec_lineU [IsDomain (W ⧸ Ideal.span {t})] :
    IsIntegral (Spec (CommRingCat.of (CrossingQuotient W t ⧸ Ideal.span {U t}))) := by
  obtain ⟨⟨E, -⟩, -⟩ := MvPolynomial.CrossingQuotient.exists_algEquiv_quotient_span_U_and_span_V_polynomial t
  haveI : IsDomain (CrossingQuotient W t ⧸ Ideal.span {U t}) :=
    MulEquiv.isDomain (Polynomial (W ⧸ Ideal.span {t})) E.toMulEquiv
  exact (affine_isIntegral_iff _).mpr ‹_›

section chartPieceU

variable (e : ℕ) (he : 0 < e) {Uc : Scheme.{w}} (f : Uc ⟶ crossingScheme (t ^ e)) [Etale f]

theorem isReduced_chartPiece_strictU [IsDomain (W ⧸ Ideal.span {t})] :
    IsReduced (pullback (pullback.snd f (toCrossing t e)) (strictUι t e he)) := by
  obtain ⟨eF, -⟩ := exists_iso_spec_lineU t
  haveI : IsDomain (Polynomial (W ⧸ Ideal.span {t})) := inferInstance
  haveI : Etale (pullback.snd (pullback.snd f (toCrossing t e)) (strictUι t e he) ≫ eF.hom) := inferInstance
  exact isReduced_of_etale (pullback.snd (pullback.snd f (toCrossing t e)) (strictUι t e he) ≫ eF.hom)

theorem strictUι_toSpec :
    strictUι t e he ≫ toSpec t e = Spec.map (CommRingCat.ofHom (algebraMap W (CrossingQuotient W t ⧸ Ideal.span {U t}))) := by
  rw [strictUι, Category.assoc, ι_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

variable (hmax : (Ideal.span {t}).IsMaximal) {κ : Type w} [Field κ] (toκ : W →+* κ) (htoκ : toκ t = 0)

include hmax htoκ in

theorem isReduced_pullback_chartPiece_strictU_fibre :
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
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.V3Glue P2MW.S_V3Asm_strict_iso_zero.V3Glue.ChartInput P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme.IdealSheafData"

end MvPolynomial.CrossingQuotient.Resolution
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.V3Glue P2MW.S_V3Asm_strict_iso_zero.V3Glue.ChartInput P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme.IdealSheafData"
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.V3Glue P2MW.S_V3Asm_strict_iso_zero.V3Glue.ChartInput P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme.IdealSheafData"
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.V3Glue P2MW.S_V3Asm_strict_iso_zero.V3Glue.ChartInput P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme.IdealSheafData"

end
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.V3Glue P2MW.S_V3Asm_strict_iso_zero.V3Glue.ChartInput P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme.IdealSheafData"

namespace V3Glue
p2m_export "V3Glue" "Site.XO Site.Node Site.xpt ChartInput.ηG_inl ChartInput.compG ChartInput.coe_support_compG ChartInput"
namespace Site
p2m_export "V3Glue.Site" "XO Node xpt HasOrientedCrossingCharts ModelHyps EtNbhd chartData rawChartInputOfDR chartInputOfDR"
p2m_open "V3Glue.Site V3Glue"

p2m_open "ModularCurve MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial"

section Orient

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ]
  (bc : pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))) ⟶ XO p O)
  [Finite (Node p 𝔛 κ)]
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)}) (M : ModelHyps p O)
  (hC : HasOrientedCrossingCharts p 𝔛 O κ bc) (ET : EtNbhd)
  (hxinj : Function.Injective (fun n : Node p 𝔛 κ => xpt 𝔛 bc n))
  (hxcl : ∀ n : Node p 𝔛 κ, IsClosed ({xpt 𝔛 bc n} : Set (XO p O)))

noncomputable def toChartU (n : Node p 𝔛 κ) (y : (chartInputOfDR p 𝔛 O κ bc hϖ M hC ET hxinj hxcl).U n) : (chartData p 𝔛 O κ bc hC n).U :=
  ((XO p O).homOfLE ((rawChartInputOfDR p 𝔛 O κ bc hϖ M hC hxinj hxcl).U_le
    ((rawChartInputOfDR p 𝔛 O κ bc hϖ M hC hxinj hxcl).hnbhd_of ET) n)).base y

theorem coe_toChartU (n : Node p 𝔛 κ) (y : (chartInputOfDR p 𝔛 O κ bc hϖ M hC ET hxinj hxcl).U n) :
    ((toChartU p 𝔛 O κ bc hϖ M hC ET hxinj hxcl n y : (chartData p 𝔛 O κ bc hC n).U) : XO p O) = (y : XO p O) := by
  unfold toChartU
  have h3 := congr($((XO p O).homOfLE_ι ((rawChartInputOfDR p 𝔛 O κ bc hϖ M hC hxinj hxcl).U_le
        ((rawChartInputOfDR p 𝔛 O κ bc hϖ M hC hxinj hxcl).hnbhd_of ET) n)).base y)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h3
  exact h3

theorem ι_toChartU (n : Node p 𝔛 κ) (y : (chartInputOfDR p 𝔛 O κ bc hϖ M hC ET hxinj hxcl).U n) :
    ((chartData p 𝔛 O κ bc hC n).U).ι.base (toChartU p 𝔛 O κ bc hϖ M hC ET hxinj hxcl n y) = (y : XO p O) :=
  coe_toChartU p 𝔛 O κ bc hϖ M hC ET hxinj hxcl n y

theorem chartInputOfDR_f_base (n : Node p 𝔛 κ) (y : (chartInputOfDR p 𝔛 O κ bc hϖ M hC ET hxinj hxcl).U n) :
    ((chartInputOfDR p 𝔛 O κ bc hϖ M hC ET hxinj hxcl).f n).base y =
      (chartData p 𝔛 O κ bc hC n).f.base (toChartU p 𝔛 O κ bc hϖ M hC ET hxinj hxcl n y) := rfl

private theorem _root_.V3Glue.Site.orient_inf (n : Node p 𝔛 κ) (y : (chartInputOfDR p 𝔛 O κ bc hϖ M hC ET hxinj hxcl).U n)
    (h : CrossingQuotient.V (((p : ℕ) : O) ^ (chartData p 𝔛 O κ bc hC n).e) ∈
      (((chartInputOfDR p 𝔛 O κ bc hϖ M hC ET hxinj hxcl).f n).base y).asIdeal) :
    (y : XO p O) ∈ Set.range (𝔛.compInf κ ≫ bc).base := by
  rw [← coe_toChartU p 𝔛 O κ bc hϖ M hC ET hxinj hxcl n y]
  (first | exact (chartData p 𝔛 O κ bc hC n).orient_inf _ h | simpa using (chartData p 𝔛 O κ bc hC n).orient_inf _ h | (have h__ := (chartData p 𝔛 O κ bc hC n).orient_inf _ h; simp at h__; exact h__))

p2m_export "V3Glue.Site" "orient_inf"
private theorem _root_.V3Glue.Site.orient_zero (n : Node p 𝔛 κ) (y : (chartInputOfDR p 𝔛 O κ bc hϖ M hC ET hxinj hxcl).U n)
    (h : CrossingQuotient.U (((p : ℕ) : O) ^ (chartData p 𝔛 O κ bc hC n).e) ∈
      (((chartInputOfDR p 𝔛 O κ bc hϖ M hC ET hxinj hxcl).f n).base y).asIdeal) :
    (y : XO p O) ∈ Set.range (𝔛.compZero κ ≫ bc).base := by
  rw [← coe_toChartU p 𝔛 O κ bc hϖ M hC ET hxinj hxcl n y]
  (first | exact (chartData p 𝔛 O κ bc hC n).orient_zero _ h | simpa using (chartData p 𝔛 O κ bc hC n).orient_zero _ h | (have h__ := (chartData p 𝔛 O κ bc hC n).orient_zero _ h; simp at h__; exact h__))

p2m_export "V3Glue.Site" "orient_zero"
private theorem _root_.V3Glue.Site.orient_inf_conv (n : Node p 𝔛 κ) (y : (chartInputOfDR p 𝔛 O κ bc hϖ M hC ET hxinj hxcl).U n)
    (h : (y : XO p O) ∈ Set.range (𝔛.compInf κ ≫ bc).base) :
    CrossingQuotient.V (((p : ℕ) : O) ^ (chartData p 𝔛 O κ bc hC n).e) ∈
      (((chartInputOfDR p 𝔛 O κ bc hϖ M hC ET hxinj hxcl).f n).base y).asIdeal := by
  refine (chartData p 𝔛 O κ bc hC n).orient_inf_conv (toChartU p 𝔛 O κ bc hϖ M hC ET hxinj hxcl n y) ?_
  rw [ι_toChartU]; exact h

p2m_export "V3Glue.Site" "orient_inf_conv"
private theorem _root_.V3Glue.Site.orient_zero_conv (n : Node p 𝔛 κ) (y : (chartInputOfDR p 𝔛 O κ bc hϖ M hC ET hxinj hxcl).U n)
    (h : (y : XO p O) ∈ Set.range (𝔛.compZero κ ≫ bc).base) :
    CrossingQuotient.U (((p : ℕ) : O) ^ (chartData p 𝔛 O κ bc hC n).e) ∈
      (((chartInputOfDR p 𝔛 O κ bc hϖ M hC ET hxinj hxcl).f n).base y).asIdeal := by
  refine (chartData p 𝔛 O κ bc hC n).orient_zero_conv (toChartU p 𝔛 O κ bc hϖ M hC ET hxinj hxcl n y) ?_
  rw [ι_toChartU]; exact h

p2m_export "V3Glue.Site" "orient_zero_conv"
end Orient
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.V3Glue P2MW.S_V3Asm_strict_iso_zero.V3Glue.ChartInput P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme.IdealSheafData"

end V3Glue.Site
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.V3Glue P2MW.S_V3Asm_strict_iso_zero.V3Glue.ChartInput P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme.IdealSheafData"
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.V3Glue P2MW.S_V3Asm_strict_iso_zero.V3Glue.ChartInput P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme.IdealSheafData"

noncomputable section

namespace V3Asm
p2m_export "V3Asm" "πX bc bc_fst SiteHyps R C D Y toDR toBase hq hRF ξ gRes hgRes comp"
p2m_open "V3Asm"

p2m_open "ModularCurve MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient"

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
  (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
  (H : SiteHyps p 𝔛 O κ toκ) (hξ : ∀ j, ξ p 𝔛 O κ toκ j ∈ (C p 𝔛 O κ toκ hϖ H).X0)

include p 𝔛 O hϖ κ toκ H hξ

theorem etale_f (n : V3Glue.Site.Node p 𝔛 κ) : Etale ((C p 𝔛 O κ toκ hϖ H).f n) := by
  haveI := H.nodeFinite
  exact (R p 𝔛 O κ toκ hϖ H).etale_toChartInput_f ((R p 𝔛 O κ toκ hϖ H).hnbhd_of H.ET) n

theorem comp_integral' : ∀ v, IsIntegral (comp p 𝔛 O κ toκ hϖ H hξ v).subscheme := fun v => by
  unfold comp V3Glue.ChartInput.compG
  exact Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure_singleton _

theorem isPullback_bc :
    IsPullback (bc p O κ toκ) (pullback.snd _ _) (πX p O) (Spec.map (CommRingCat.ofHom toκ)) :=
  AlgebraicGeometry.isPullback_map_snd_snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))
    (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))) (Spec.map (CommRingCat.ofHom toκ))
    (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext_int _ _)

theorem ker_toκ : RingHom.ker toκ = IsLocalRing.maximalIdeal O := by
  refine ((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (RingHom.ker_ne_top toκ) ?_).symm
  rw [hϖ, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]

theorem range_bc : Set.range (bc p O κ toκ).base = (πX p O).base ⁻¹' {IsLocalRing.closedPoint O} := by
  rw [AlgebraicGeometry.IsPullback.range_fst' (isPullback_bc p 𝔛 O hϖ κ toκ H hξ),
    AlgebraicGeometry.range_specMap_of_ker_eq_maximalIdeal toκ (ker_toκ p 𝔛 O hϖ κ toκ H hξ)]

theorem πX_bc_apply (w : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))))) :
    (πX p O).base ((bc p O κ toκ).base w) = IsLocalRing.closedPoint O := by
  have hw : (bc p O κ toκ).base w ∈ Set.range (bc p O κ toκ).base := ⟨w, rfl⟩
  rw [range_bc p 𝔛 O hϖ κ toκ H hξ] at hw
  exact hw

abbrev iB : Spec (CommRingCat.of (O ⧸ IsLocalRing.maximalIdeal O)) ⟶ Spec (CommRingCat.of O) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)))

theorem iB_isClosedImmersion : IsClosedImmersion (iB O) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

theorem iB_mono : Mono (iB O) := by
  haveI : Epi (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O))) :=
    ConcreteCategory.epi_of_surjective _ Ideal.Quotient.mk_surjective
  show Mono (Scheme.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O))).op)
  infer_instance

def resκ : O ⧸ IsLocalRing.maximalIdeal O →+* κ :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) toκ (fun a ha => by
    rwa [← ker_toκ p 𝔛 O hϖ κ toκ H hξ, RingHom.mem_ker] at ha)

theorem resκ_comp_mk : (resκ p 𝔛 O hϖ κ toκ H hξ).comp (Ideal.Quotient.mk _) = toκ := Ideal.Quotient.lift_comp_mk _ _ _

abbrev aB : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of (O ⧸ IsLocalRing.maximalIdeal O)) :=
  Spec.map (CommRingCat.ofHom (resκ p 𝔛 O hϖ κ toκ H hξ))

theorem aB_flat : Flat (aB p 𝔛 O hϖ κ toκ H hξ) := by
  letI : Field (O ⧸ IsLocalRing.maximalIdeal O) := Ideal.Quotient.field _
  letI := (resκ p 𝔛 O hϖ κ toκ H hξ).toAlgebra
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap (O ⧸ IsLocalRing.maximalIdeal O) κ)))
  infer_instance

theorem specMap_toκ_eq : Spec.map (CommRingCat.ofHom toκ) = aB p 𝔛 O hϖ κ toκ H hξ ≫ iB O := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, resκ_comp_mk]

theorem isDomain_quot_p : IsDomain (O ⧸ Ideal.span {((p : ℕ) : O)}) := by
  rw [← hϖ]; infer_instance

abbrev lamInf (n : V3Glue.Site.Node p 𝔛 κ) :
    Spec (CommRingCat.of (CrossingQuotient O ((p : ℕ) : O) ⧸ Ideal.span {CrossingQuotient.V ((p : ℕ) : O)})) ⟶
      (C p 𝔛 O κ toκ hϖ H).Res n :=
  MvPolynomial.CrossingQuotient.Resolution.strictVι ((p : ℕ) : O) ((C p 𝔛 O κ toκ hϖ H).thick n)
    ((C p 𝔛 O κ toκ hϖ H).one_le_thick n)

abbrev lamZero (n : V3Glue.Site.Node p 𝔛 κ) :
    Spec (CommRingCat.of (CrossingQuotient O ((p : ℕ) : O) ⧸ Ideal.span {CrossingQuotient.U ((p : ℕ) : O)})) ⟶
      (C p 𝔛 O κ toκ hϖ H).Res n :=
  MvPolynomial.CrossingQuotient.Resolution.strictUι ((p : ℕ) : O) ((C p 𝔛 O κ toκ hϖ H).thick n)
    ((C p 𝔛 O κ toκ hϖ H).one_le_thick n)

theorem lamInf_isClosedImmersion (n : V3Glue.Site.Node p 𝔛 κ) : IsClosedImmersion (lamInf p 𝔛 O hϖ κ toκ H n) :=
  MvPolynomial.CrossingQuotient.Resolution.isClosedImmersion_strictVι _ _ _
theorem lamZero_isClosedImmersion (n : V3Glue.Site.Node p 𝔛 κ) : IsClosedImmersion (lamZero p 𝔛 O hϖ κ toκ H n) :=
  MvPolynomial.CrossingQuotient.Resolution.isClosedImmersion_strictUι _ _ _
theorem lamInf_ρ_isClosedImmersion (n : V3Glue.Site.Node p 𝔛 κ) : IsClosedImmersion (lamInf p 𝔛 O hϖ κ toκ H n ≫ (C p 𝔛 O κ toκ hϖ H).ρ n) :=
  MvPolynomial.CrossingQuotient.Resolution.isClosedImmersion_strictVι_toCrossing _ _ _
theorem lamZero_ρ_isClosedImmersion (n : V3Glue.Site.Node p 𝔛 κ) : IsClosedImmersion (lamZero p 𝔛 O hϖ κ toκ H n ≫ (C p 𝔛 O κ toκ hϖ H).ρ n) :=
  MvPolynomial.CrossingQuotient.Resolution.isClosedImmersion_strictUι_toCrossing _ _ _

theorem isReduced_pieceInf (n : V3Glue.Site.Node p 𝔛 κ) :
    IsReduced (pullback ((C p 𝔛 O κ toκ hϖ H).g n) (lamInf p 𝔛 O hϖ κ toκ H n)) := by
  exact @MvPolynomial.CrossingQuotient.Resolution.isReduced_chartPiece_strictV O _ ((p : ℕ) : O)
    ((C p 𝔛 O κ toκ hϖ H).thick n) ((C p 𝔛 O κ toκ hϖ H).one_le_thick n) _
    ((C p 𝔛 O κ toκ hϖ H).f n) (etale_f p 𝔛 O hϖ κ toκ H hξ n) (isDomain_quot_p p 𝔛 O hϖ κ toκ H hξ)

theorem isReduced_pieceZero (n : V3Glue.Site.Node p 𝔛 κ) :
    IsReduced (pullback ((C p 𝔛 O κ toκ hϖ H).g n) (lamZero p 𝔛 O hϖ κ toκ H n)) := by
  exact @MvPolynomial.CrossingQuotient.Resolution.isReduced_chartPiece_strictU O _ ((p : ℕ) : O)
    ((C p 𝔛 O κ toκ hϖ H).thick n) ((C p 𝔛 O κ toκ hϖ H).one_le_thick n) _
    ((C p 𝔛 O κ toκ hϖ H).f n) (etale_f p 𝔛 O hϖ κ toκ H hξ n) (isDomain_quot_p p 𝔛 O hϖ κ toκ H hξ)

theorem hGκ_inf (n : V3Glue.Site.Node p 𝔛 κ) :
    IsReduced (pullback (pullback.fst ((C p 𝔛 O κ toκ hϖ H).g n) (lamInf p 𝔛 O hϖ κ toκ H n) ≫
      (C p 𝔛 O κ toκ hϖ H).toB n) (Spec.map (CommRingCat.ofHom toκ))) := by
  exact @MvPolynomial.CrossingQuotient.Resolution.isReduced_pullback_chartPiece_strictV_fibre O _ ((p : ℕ) : O)
    ((C p 𝔛 O κ toκ hϖ H).thick n) ((C p 𝔛 O κ toκ hϖ H).one_le_thick n) _
    ((C p 𝔛 O κ toκ hϖ H).f n) (etale_f p 𝔛 O hϖ κ toκ H hξ n)
    (hϖ ▸ IsLocalRing.maximalIdeal.isMaximal O) κ _ toκ (by rw [map_natCast, CharP.cast_eq_zero])

theorem hGκ_zero (n : V3Glue.Site.Node p 𝔛 κ) :
    IsReduced (pullback (pullback.fst ((C p 𝔛 O κ toκ hϖ H).g n) (lamZero p 𝔛 O hϖ κ toκ H n) ≫
      (C p 𝔛 O κ toκ hϖ H).toB n) (Spec.map (CommRingCat.ofHom toκ))) := by
  exact @MvPolynomial.CrossingQuotient.Resolution.isReduced_pullback_chartPiece_strictU_fibre O _ ((p : ℕ) : O)
    ((C p 𝔛 O κ toκ hϖ H).thick n) ((C p 𝔛 O κ toκ hϖ H).one_le_thick n) _
    ((C p 𝔛 O κ toκ hϖ H).f n) (etale_f p 𝔛 O hϖ κ toκ H hξ n)
    (hϖ ▸ IsLocalRing.maximalIdeal.isMaximal O) κ _ toκ (by rw [map_natCast, CharP.cast_eq_zero])

theorem horientInf_fwd (n : V3Glue.Site.Node p 𝔛 κ) (y : (C p 𝔛 O κ toκ hϖ H).U n)
    (h : ((C p 𝔛 O κ toκ hϖ H).f n).base y ∈
      Set.range (lamInf p 𝔛 O hϖ κ toκ H n ≫ (C p 𝔛 O κ toκ hϖ H).ρ n).base) :
    (y : V3Glue.Site.XO p O) ∈ Set.range (𝔛.compInf κ ≫ bc p O κ toκ).base := by
  haveI := H.nodeFinite
  exact V3Glue.Site.orient_inf p 𝔛 O κ (bc p O κ toκ) hϖ H.model H.hC H.ET H.hxinj H.hxcl n y
    ((MvPolynomial.CrossingQuotient.Resolution.mem_range_strictVι_toCrossing_iff _ _ _ _).mp h)

theorem horientInf_conv (n : V3Glue.Site.Node p 𝔛 κ) (y : (C p 𝔛 O κ toκ hϖ H).U n)
    (h : (y : V3Glue.Site.XO p O) ∈ Set.range (𝔛.compInf κ ≫ bc p O κ toκ).base) :
    ((C p 𝔛 O κ toκ hϖ H).f n).base y ∈
      Set.range (lamInf p 𝔛 O hϖ κ toκ H n ≫ (C p 𝔛 O κ toκ hϖ H).ρ n).base := by
  haveI := H.nodeFinite
  exact (MvPolynomial.CrossingQuotient.Resolution.mem_range_strictVι_toCrossing_iff _ _ _ _).mpr
    (V3Glue.Site.orient_inf_conv p 𝔛 O κ (bc p O κ toκ) hϖ H.model H.hC H.ET H.hxinj H.hxcl n y h)

theorem horientZero_fwd (n : V3Glue.Site.Node p 𝔛 κ) (y : (C p 𝔛 O κ toκ hϖ H).U n)
    (h : ((C p 𝔛 O κ toκ hϖ H).f n).base y ∈
      Set.range (lamZero p 𝔛 O hϖ κ toκ H n ≫ (C p 𝔛 O κ toκ hϖ H).ρ n).base) :
    (y : V3Glue.Site.XO p O) ∈ Set.range (𝔛.compZero κ ≫ bc p O κ toκ).base := by
  haveI := H.nodeFinite
  exact V3Glue.Site.orient_zero p 𝔛 O κ (bc p O κ toκ) hϖ H.model H.hC H.ET H.hxinj H.hxcl n y
    ((MvPolynomial.CrossingQuotient.Resolution.mem_range_strictUι_toCrossing_iff _ _ _ _).mp h)

theorem horientZero_conv (n : V3Glue.Site.Node p 𝔛 κ) (y : (C p 𝔛 O κ toκ hϖ H).U n)
    (h : (y : V3Glue.Site.XO p O) ∈ Set.range (𝔛.compZero κ ≫ bc p O κ toκ).base) :
    ((C p 𝔛 O κ toκ hϖ H).f n).base y ∈
      Set.range (lamZero p 𝔛 O hϖ κ toκ H n ≫ (C p 𝔛 O κ toκ hϖ H).ρ n).base := by
  haveI := H.nodeFinite
  exact (MvPolynomial.CrossingQuotient.Resolution.mem_range_strictUι_toCrossing_iff _ _ _ _).mpr
    (V3Glue.Site.orient_zero_conv p 𝔛 O κ (bc p O κ toκ) hϖ H.model H.hC H.ET H.hxinj H.hxcl n y h)

theorem x_mem_range_compInf (n : V3Glue.Site.Node p 𝔛 κ) :
    (C p 𝔛 O κ toκ hϖ H).x n ∈ Set.range (𝔛.compInf κ ≫ bc p O κ toκ).base :=
  ⟨(pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n, rfl⟩

theorem x_mem_range_compZero (n : V3Glue.Site.Node p 𝔛 κ) :
    (C p 𝔛 O κ toκ hϖ H).x n ∈ Set.range (𝔛.compZero κ ≫ bc p O κ toκ).base :=
  ⟨(pullback.snd (𝔛.compInf κ) (𝔛.compZero κ)).base n, by
    show ((pullback.snd _ _ ≫ 𝔛.compZero κ) ≫ bc p O κ toκ).base n = _
    rw [← pullback.condition]; rfl⟩

theorem nonempty_node : Nonempty (V3Glue.Site.Node p 𝔛 κ) := by
  classical
  have h : Nat.card (V3Glue.Site.Node p 𝔛 κ) ≠ 0 := by
    rw [𝔛.crossing_card κ]
    haveI : Finite ↥(ssJSet p κ) := (ssJSet_finite p κ).to_subtype
    haveI : Nonempty ↥(ssJSet p κ) := (ssJSet_nonempty (q := p) (k := κ)).to_subtype
    exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
  exact (Nat.card_ne_zero.mp h).1

theorem exists_factor_comp_inl (j : Fin 2) :
    ∃ s₀ : (comp p 𝔛 O κ toκ hϖ H hξ (Sum.inl j)).subscheme ⟶ Spec (CommRingCat.of (O ⧸ IsLocalRing.maximalIdeal O)),
      (comp p 𝔛 O κ toκ hϖ H hξ (Sum.inl j)).subschemeι ≫ toDR p 𝔛 O κ toκ hϖ H ≫ πX p O = s₀ ≫ iB O := by
  unfold toDR D

  have hS : Set.range (comp p 𝔛 O κ toκ hϖ H hξ (Sum.inl j)).subschemeι.base =
      closure {(C p 𝔛 O κ toκ hϖ H).toGlueInput.ιX0.base ⟨ξ p 𝔛 O κ toκ j, hξ j⟩} := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    unfold comp
    erw [V3Glue.ChartInput.coe_support_compG, V3Glue.ChartInput.ηG_inl]
  have hy : (toDR p 𝔛 O κ toκ hϖ H ≫ πX p O).base
      ((C p 𝔛 O κ toκ hϖ H).toGlueInput.ιX0.base ⟨ξ p 𝔛 O κ toκ j, hξ j⟩) = IsLocalRing.closedPoint O := by
    have h1 := congr($((C p 𝔛 O κ toκ hϖ H).toGlueInput.ιX0_toDR).base ⟨ξ p 𝔛 O κ toκ j, hξ j⟩)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h1 ⊢
    erw [h1]

    refine Fin.cases ?_ (fun i => ?_) j <;> exact πX_bc_apply p 𝔛 O hϖ κ toκ H hξ _
  have hall := AlgebraicGeometry.forall_comp_eq_of_range_eq_closure _ (toDR p 𝔛 O κ toκ hϖ H ≫ πX p O) hS hy
    (IsLocalRing.isClosed_singleton_closedPoint O)
  haveI : IsReduced (comp p 𝔛 O κ toκ hϖ H hξ (Sum.inl j)).subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  obtain ⟨s₀, hs₀⟩ := AlgebraicGeometry.exists_lift_specQuotient
    ((comp p 𝔛 O κ toκ hϖ H hξ (Sum.inl j)).subschemeι ≫ toDR p 𝔛 O κ toκ hϖ H ≫ πX p O)
    (IsLocalRing.maximalIdeal O)
    (fun r hr => AlgebraicGeometry.preimage_basicOpen_eq_bot_of_forall_eq_closedPoint _ hall r hr)
  exact ⟨s₀, hs₀.symm⟩

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem strict_iso_inf : ∃ e : pullback ((comp p 𝔛 O κ toκ hϖ H hξ (Sum.inl 0)).subschemeι ≫ toBase p 𝔛 O κ toκ hϖ H) (Spec.map (CommRingCat.ofHom toκ)) ⟶ (𝔛.ratModel κ).C,
    IsIso e ∧ e ≫ (𝔛.ratModel κ).toBase = pullback.snd _ _ ∧
      e ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ = pullback.fst _ _ ≫ (comp p 𝔛 O κ toκ hϖ H hξ (Sum.inl 0)).subschemeι ≫ toDR p 𝔛 O κ toκ hϖ H := by
  unfold toBase toDR D comp
  obtain ⟨n₀⟩ := nonempty_node p 𝔛 O hϖ κ toκ H hξ
  haveI : ∀ n, IsReduced (pullback ((C p 𝔛 O κ toκ hϖ H).g n) (lamInf p 𝔛 O hϖ κ toκ H n)) :=
    fun n => isReduced_pieceInf p 𝔛 O hϖ κ toκ H hξ n
  haveI : @Mono Scheme _ _ (C p 𝔛 O κ toκ hϖ H).B (iB O) := iB_mono p 𝔛 O hϖ κ toκ H hξ
  haveI : Flat (aB p 𝔛 O hϖ κ toκ H hξ) := aB_flat p 𝔛 O hϖ κ toκ H hξ
  haveI : ∀ n, IsClosedImmersion (lamInf p 𝔛 O hϖ κ toκ H n) := fun n => lamInf_isClosedImmersion p 𝔛 O hϖ κ toκ H hξ n
  haveI : ∀ n, IsClosedImmersion (lamInf p 𝔛 O hϖ κ toκ H n ≫ (C p 𝔛 O κ toκ hϖ H).ρ n) :=
    fun n => lamInf_ρ_isClosedImmersion p 𝔛 O hϖ κ toκ H hξ n
  obtain ⟨s₀, hs₀⟩ := exists_factor_comp_inl p 𝔛 O hϖ κ toκ H hξ 0
  haveI := 𝔛.compInf_isClosedImmersion κ
  obtain ⟨e, he₁, he₂, he₃⟩ := (C p 𝔛 O κ toκ hϖ H).strict_iso_of
    (hRF p 𝔛 O κ toκ hϖ H) (gRes p 𝔛 O κ toκ hϖ H) (hgRes p 𝔛 O κ toκ hϖ H)
    (ξ p 𝔛 O κ toκ) hξ 0
    (𝔛.compInf κ) (bc p O κ toκ) (pullback.snd _ _) (Spec.map (CommRingCat.ofHom toκ)) (isPullback_bc p 𝔛 O hϖ κ toκ H hξ)
    rfl
    (DRModelPackage.preimage_closure_image_range_compInf_eq_of_comp_fst_eq p 𝔛 O κ (bc p O κ toκ)
      (bc_fst p O κ toκ)).1
    (IsLocalRing.isClosed_singleton_closedPoint O) (range_bc p 𝔛 O hϖ κ toκ H hξ)
    (fun r => πX_bc_apply p 𝔛 O hϖ κ toκ H hξ _)
    (lamInf p 𝔛 O hϖ κ toκ H) (horientInf_fwd p 𝔛 O hϖ κ toκ H hξ) (horientInf_conv p 𝔛 O hϖ κ toκ H hξ)
    (x_mem_range_compInf p 𝔛 O hϖ κ toκ H hξ)
    n₀ (iB O) (aB p 𝔛 O hϖ κ toκ H hξ) (specMap_toκ_eq p 𝔛 O hϖ κ toκ H hξ) s₀ hs₀ (hGκ_inf p 𝔛 O hϖ κ toκ H hξ n₀)
  refine ⟨e, he₁, ?_, he₃⟩
  rw [← 𝔛.compInf_over κ]
  exact he₂

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem strict_iso_zero : ∃ e : pullback ((comp p 𝔛 O κ toκ hϖ H hξ (Sum.inl 1)).subschemeι ≫ toBase p 𝔛 O κ toκ hϖ H) (Spec.map (CommRingCat.ofHom toκ)) ⟶ (𝔛.ratModel κ).C,
    IsIso e ∧ e ≫ (𝔛.ratModel κ).toBase = pullback.snd _ _ ∧
      e ≫ 𝔛.compZero κ ≫ DRModel.baseChangeMap toκ = pullback.fst _ _ ≫ (comp p 𝔛 O κ toκ hϖ H hξ (Sum.inl 1)).subschemeι ≫ toDR p 𝔛 O κ toκ hϖ H := by
  unfold toBase toDR D comp
  obtain ⟨n₀⟩ := nonempty_node p 𝔛 O hϖ κ toκ H hξ
  haveI : ∀ n, IsReduced (pullback ((C p 𝔛 O κ toκ hϖ H).g n) (lamZero p 𝔛 O hϖ κ toκ H n)) :=
    fun n => isReduced_pieceZero p 𝔛 O hϖ κ toκ H hξ n
  haveI : @Mono Scheme _ _ (C p 𝔛 O κ toκ hϖ H).B (iB O) := iB_mono p 𝔛 O hϖ κ toκ H hξ
  haveI : Flat (aB p 𝔛 O hϖ κ toκ H hξ) := aB_flat p 𝔛 O hϖ κ toκ H hξ
  haveI : ∀ n, IsClosedImmersion (lamZero p 𝔛 O hϖ κ toκ H n) := fun n => lamZero_isClosedImmersion p 𝔛 O hϖ κ toκ H hξ n
  haveI : ∀ n, IsClosedImmersion (lamZero p 𝔛 O hϖ κ toκ H n ≫ (C p 𝔛 O κ toκ hϖ H).ρ n) :=
    fun n => lamZero_ρ_isClosedImmersion p 𝔛 O hϖ κ toκ H hξ n
  obtain ⟨s₀, hs₀⟩ := exists_factor_comp_inl p 𝔛 O hϖ κ toκ H hξ 1
  haveI := 𝔛.compZero_isClosedImmersion κ
  obtain ⟨e, he₁, he₂, he₃⟩ := (C p 𝔛 O κ toκ hϖ H).strict_iso_of
    (hRF p 𝔛 O κ toκ hϖ H) (gRes p 𝔛 O κ toκ hϖ H) (hgRes p 𝔛 O κ toκ hϖ H)
    (ξ p 𝔛 O κ toκ) hξ 1
    (𝔛.compZero κ) (bc p O κ toκ) (pullback.snd _ _) (Spec.map (CommRingCat.ofHom toκ)) (isPullback_bc p 𝔛 O hϖ κ toκ H hξ)
    rfl
    (DRModelPackage.preimage_closure_image_range_compInf_eq_of_comp_fst_eq p 𝔛 O κ (bc p O κ toκ)
      (bc_fst p O κ toκ)).2
    (IsLocalRing.isClosed_singleton_closedPoint O) (range_bc p 𝔛 O hϖ κ toκ H hξ)
    (fun r => πX_bc_apply p 𝔛 O hϖ κ toκ H hξ _)
    (lamZero p 𝔛 O hϖ κ toκ H) (horientZero_fwd p 𝔛 O hϖ κ toκ H hξ) (horientZero_conv p 𝔛 O hϖ κ toκ H hξ)
    (x_mem_range_compZero p 𝔛 O hϖ κ toκ H hξ)
    n₀ (iB O) (aB p 𝔛 O hϖ κ toκ H hξ) (specMap_toκ_eq p 𝔛 O hϖ κ toκ H hξ) s₀ hs₀ (hGκ_zero p 𝔛 O hϖ κ toκ H hξ n₀)
  refine ⟨e, he₁, ?_, he₃⟩
  rw [← 𝔛.compZero_over κ]
  exact he₂

end V3Asm
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.V3Glue P2MW.S_V3Asm_strict_iso_zero.V3Glue.ChartInput P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme.IdealSheafData"

end
p2m_reactivate "P2MW.S_V3Asm_strict_iso_zero.MvPolynomial P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_strict_iso_zero.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry P2MW.S_V3Asm_strict_iso_zero.V3Glue P2MW.S_V3Asm_strict_iso_zero.V3Glue.ChartInput P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme P2MW.S_V3Asm_strict_iso_zero.AlgebraicGeometry.Scheme.IdealSheafData"

theorem solution (p : ℕ) [Fact p.Prime] (𝔛 : ModularCurve.DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (H : V3Asm.SiteHyps p 𝔛 O κ toκ) (hξ : ∀ j, V3Asm.ξ p 𝔛 O κ toκ j ∈ (V3Asm.C p 𝔛 O κ toκ hϖ H).X0) :
    ∃ e : pullback ((V3Asm.comp p 𝔛 O κ toκ hϖ H hξ (Sum.inl 1)).subschemeι ≫ (V3Asm.toBase p 𝔛 O κ toκ hϖ H)) (Spec.map (CommRingCat.ofHom toκ)) ⟶ (𝔛.ratModel κ).C,
      IsIso e ∧ e ≫ (𝔛.ratModel κ).toBase = pullback.snd _ _ ∧
        e ≫ 𝔛.compZero κ ≫ ModularCurve.DRModel.baseChangeMap toκ = pullback.fst _ _ ≫ (V3Asm.comp p 𝔛 O κ toκ hϖ H hξ (Sum.inl 1)).subschemeι ≫ (V3Asm.toDR p 𝔛 O κ toκ hϖ H) :=
  V3Asm.strict_iso_zero p 𝔛 O hϖ κ toκ H hξ

end S_V3Asm_strict_iso_zero
end P2MW
export P2MW.S_V3Asm_strict_iso_zero (solution)
