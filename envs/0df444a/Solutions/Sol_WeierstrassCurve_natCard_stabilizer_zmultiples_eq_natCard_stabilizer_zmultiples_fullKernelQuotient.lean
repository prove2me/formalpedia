-- Prove2me | solution 1 for WeierstrassCurve.natCard_stabilizer_zmultiples_eq_natCard_stabilizer_zmultiples_fullKernelQuotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/ee591135-28ac-5e2d-a618-0e421c11f486

import Mathlib
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_VeluVariableChange
import Theorems.Thm_WeierstrassCurve_variableChange_veluQuotientOfSums_asymWeights
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_WeierstrassCurve_exists_fullKernelHom
import Theorems.Thm_WeierstrassCurve_fullKernelQuotient_discriminant_ne_zero
import Theorems.Thm_WeierstrassCurve_fullKernelHom_surjective_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_variableChange_eq_fullKernelQuotient_fullKernelQuotient_comp_eq_smul
import Theorems.Thm_WeierstrassCurve_exists_nsmul_eq_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_finite_stabilizer_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_natCard_stabilizer_zmultiples_eq_natCard_stabilizer_zmultiples_fullKernelQuotient
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsDiscreteValuationRingSubtypeFunctionFieldMemValuationSubringValuationSubringWithZeroMultiplicativeIntValuationInfty WeierstrassCurve.Affine.valuationInfty_isNontrivial WeierstrassCurve.veluQuotient2_isShortNF WeierstrassCurve.instIsShortNFMk"
p2m_attr_erase "simp" "WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄"
p2m_attr_erase "simp" "compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

noncomputable section

namespace P2MKcStabDual

section Cast
variable {L : Type*} [Field L] [DecidableEq L]
def castPt {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) : W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst e; exact AddEquiv.refl _
theorem coordsOrZero_castPt {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    (castPt e P).coordsOrZero = P.coordsOrZero := by
  subst e; rfl
def vcInv (C : VariableChange L) (W : WeierstrassCurve L) :
    W.toAffine.Point →+ (C • W).toAffine.Point :=
  AddMonoidHom.mk' (Point.vcInvFun C W.toAffine) (Point.vcInvFun_add C W.toAffine)
theorem vcInv_injective (C : VariableChange L) (W : WeierstrassCurve L) :
    Function.Injective (vcInv C W) :=
  (Point.vcFun_rightInverse (C := C) (W := W.toAffine)).injective
theorem vcInv_eq_zero_iff (C : VariableChange L) (W : WeierstrassCurve L) (P : W.toAffine.Point) :
    vcInv C W P = 0 ↔ P = 0 := by
  constructor
  · intro h
    exact vcInv_injective C W (by rw [h, _root_.map_zero])
  · rintro rfl; exact _root_.map_zero _
theorem coordsOrZero_vcInv (C : VariableChange L) (W : WeierstrassCurve L) (P : W.toAffine.Point)
    (hP : P ≠ 0) : (vcInv C W P).coordsOrZero = vcInvEmbedding C P.coordsOrZero := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · rfl

theorem castPt_eq_iff_heq {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) (P : W₁.toAffine.Point)
    (Q : W₂.toAffine.Point) : castPt e P = Q ↔ HEq P Q := by
  subst e; exact Iff.rfl.trans heq_iff_eq.symm

theorem castPt_castPt {W₁ W₂ W₃ : WeierstrassCurve L} (e : W₁ = W₂) (e' : W₂ = W₃)
    (P : W₁.toAffine.Point) : castPt e' (castPt e P) = castPt (e.trans e') P := by
  subst e e'; rfl

theorem castPt_symm_apply {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) (P : W₂.toAffine.Point) :
    (castPt e).symm P = castPt e.symm P := by
  subst e; rfl

theorem vcInv_apply (C : VariableChange L) (W : WeierstrassCurve L) (P : W.toAffine.Point) :
    vcInv C W P = Point.vcInvFun C W.toAffine P := rfl

theorem equivOfVariableChangeEq_symm_apply {C : VariableChange L} {W V : WeierstrassCurve L}
    (h : C • W = V) (P : W.toAffine.Point) :
    (Point.equivOfVariableChangeEq (W := W.toAffine) h).symm P = castPt h (vcInv C W P) := by
  subst h; rfl

theorem equivOfVariableChangeEq_apply {C : VariableChange L} {W V : WeierstrassCurve L}
    (h : C • W = V) (P : V.toAffine.Point) :
    Point.equivOfVariableChangeEq (W := W.toAffine) h P =
      Point.vcFun C W.toAffine (castPt h.symm P) := by
  subst h; rfl
end Cast

section KernelSums
variable {A : Type*} [AddCommGroup A]
theorem mem_image_nsmul_iff {N : ℕ} {R : A} (hR : addOrderOf R = N) (hN : N ≠ 0) (T : A) :
    (∃ k, 1 ≤ k ∧ k ≤ N - 1 ∧ k • R = T) ↔ T ∈ AddSubgroup.zmultiples R ∧ T ≠ 0 := by
  classical
  have hfin : IsOfFinAddOrder R := by
    rw [← addOrderOf_pos_iff, hR]; exact Nat.pos_of_ne_zero hN
  constructor
  · rintro ⟨k, hk1, hk2, rfl⟩
    refine ⟨AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples R) k, ?_⟩
    exact nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hR]; omega)
  · rintro ⟨hT, hT0⟩
    rw [hfin.mem_zmultiples_iff_mem_range_addOrderOf, Finset.mem_image] at hT
    obtain ⟨k, hk, rfl⟩ := hT
    rw [Finset.mem_range, hR] at hk
    refine ⟨k, ?_, by omega, rfl⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact absurd (zero_nsmul R) hT0
    · exact hk0
theorem nsmul_injOn_Icc {N : ℕ} {R : A} (hR : addOrderOf R = N) :
    Set.InjOn (fun k : ℕ => k • R) (Finset.Icc 1 (N - 1) : Set ℕ) := by
  intro k hk k' hk' h
  simp only [Finset.coe_Icc, Set.mem_Icc] at hk hk'
  have h' : k % addOrderOf R = k' % addOrderOf R := nsmul_inj_mod.mp h
  rwa [hR, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
theorem image_nsmul_Icc_eq [DecidableEq A] {N : ℕ} {R R' : A} (hR : addOrderOf R = N)
    (hR' : addOrderOf R' = N) (h : AddSubgroup.zmultiples R = AddSubgroup.zmultiples R') :
    (Finset.Icc 1 (N - 1)).image (fun k : ℕ => k • R) =
      (Finset.Icc 1 (N - 1)).image (fun k : ℕ => k • R') := by
  rcases eq_or_ne N 0 with rfl | hN
  · rfl
  ext T
  simp only [Finset.mem_image, Finset.mem_Icc]
  have h1 := mem_image_nsmul_iff hR hN T
  have h2 := mem_image_nsmul_iff hR' hN T
  rw [h] at h1
  constructor
  · rintro ⟨k, ⟨hk1, hk2⟩, hk⟩
    obtain ⟨k', hk1', hk2', hk'⟩ := h2.mpr (h1.mp ⟨k, hk1, hk2, hk⟩)
    exact ⟨k', ⟨hk1', hk2'⟩, hk'⟩
  · rintro ⟨k, ⟨hk1, hk2⟩, hk⟩
    obtain ⟨k', hk1', hk2', hk'⟩ := h1.mpr (h2.mp ⟨k, hk1, hk2, hk⟩)
    exact ⟨k', ⟨hk1', hk2'⟩, hk'⟩
theorem sum_nsmul_congr {N : ℕ} {R R' : A} (hR : addOrderOf R = N) (hR' : addOrderOf R' = N)
    (h : AddSubgroup.zmultiples R = AddSubgroup.zmultiples R') {β : Type*} [AddCommMonoid β]
    (f : A → β) :
    ∑ k ∈ Finset.Icc 1 (N - 1), f (k • R) = ∑ k ∈ Finset.Icc 1 (N - 1), f (k • R') := by
  classical
  rw [← Finset.sum_image (g := fun k : ℕ => k • R) (f := f) (nsmul_injOn_Icc hR),
    ← Finset.sum_image (g := fun k : ℕ => k • R') (f := f) (nsmul_injOn_Icc hR'),
    image_nsmul_Icc_eq hR hR' h]
end KernelSums

section Quotient

variable {L : Type*} [Field L] [DecidableEq L]

theorem oddOrderSummingSet_eq_image (W : WeierstrassCurve L) (Q : W.toAffine.Point) (n : ℕ) :
    W.oddOrderSummingSet Q n =
      ((Finset.Icc 1 n).image (fun k : ℕ => k • Q)).image Point.coordsOrZero := by
  classical
  rw [oddOrderSummingSet, Finset.image_image]
  rfl

theorem fullKernelQuotient_congr (W : WeierstrassCurve L) {N : ℕ} {Q Q' : W.toAffine.Point}
    (hQ : addOrderOf Q = N) (hQ' : addOrderOf Q' = N)
    (h : AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q') :
    W.fullKernelQuotient Q N = W.fullKernelQuotient Q' N := by
  classical
  have hS : W.oddOrderSummingSet Q (N - 1) = W.oddOrderSummingSet Q' (N - 1) := by
    rw [oddOrderSummingSet_eq_image, oddOrderSummingSet_eq_image, image_nsmul_Icc_eq hQ hQ' h]
  rw [fullKernelQuotient, fullKernelQuotient, hS]

theorem fullKernelQuotient_castPt {V₁ V₂ : WeierstrassCurve L} (e : V₁ = V₂)
    (P : V₁.toAffine.Point) (N : ℕ) :
    V₂.fullKernelQuotient (castPt e P) N = V₁.fullKernelQuotient P N := by
  subst e; rfl

theorem nsmul_ne_zero_of_mem_Icc {W : WeierstrassCurve L} {N : ℕ} {Q : W.toAffine.Point}
    (hQ : addOrderOf Q = N) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ N - 1) : k • Q ≠ 0 :=
  nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)

theorem oddOrderSummingSet_vcInv (C : VariableChange L) (W : WeierstrassCurve L) {N : ℕ}
    (Q : W.toAffine.Point) (hQ : addOrderOf Q = N) :
    (C • W).oddOrderSummingSet (vcInv C W Q) (N - 1) =
      (W.oddOrderSummingSet Q (N - 1)).map (vcInvEmbedding C) := by
  ext P
  simp only [mem_oddOrderSummingSet, Finset.mem_map]
  constructor
  · rintro ⟨k, hk1, hk2, rfl⟩
    refine ⟨(k • Q).coordsOrZero, ⟨k, hk1, hk2, rfl⟩, ?_⟩
    rw [← map_nsmul, coordsOrZero_vcInv _ _ _ (nsmul_ne_zero_of_mem_Icc hQ hk1 hk2)]
  · rintro ⟨P₀, ⟨k, hk1, hk2, rfl⟩, rfl⟩
    exact ⟨k, hk1, hk2, by
      rw [← map_nsmul, coordsOrZero_vcInv _ _ _ (nsmul_ne_zero_of_mem_Icc hQ hk1 hk2)]⟩

theorem negY_mem_oddOrderSummingSet (W : WeierstrassCurve L) {N : ℕ} (Q : W.toAffine.Point)
    (hQ : addOrderOf Q = N) :
    ∀ P ∈ W.oddOrderSummingSet Q (N - 1),
      (P.1, W.toAffine.negY P.1 P.2) ∈ W.oddOrderSummingSet Q (N - 1) := by
  intro P hP
  obtain ⟨k, hk1, hk2, rfl⟩ := (mem_oddOrderSummingSet _).mp hP
  refine (mem_oddOrderSummingSet _).mpr ⟨N - k, by omega, by omega, ?_⟩
  have hneg : (N - k) • Q = -(k • Q) := by
    refine eq_neg_of_add_eq_zero_left ?_
    rw [← add_nsmul, Nat.sub_add_cancel (by omega), ← hQ, addOrderOf_nsmul_eq_zero]
  rw [hneg, coordsOrZero_neg _ (nsmul_ne_zero_of_mem_Icc hQ hk1 hk2)]

theorem fullKernelQuotient_vcInv (C : VariableChange L) (W : WeierstrassCurve L) {N : ℕ}
    (Q : W.toAffine.Point) (hQ : addOrderOf Q = N) :
    (C • W).fullKernelQuotient (vcInv C W Q) N = C • W.fullKernelQuotient Q N := by
  rw [fullKernelQuotient, fullKernelQuotient, oddOrderSummingSet_vcInv C W Q hQ]
  exact variableChange_veluQuotientOfSums_asymWeights C W _ (negY_mem_oddOrderSummingSet W Q hQ)

end Quotient

section PointCovariance

variable {L : Type*} [Field L] [DecidableEq L]

def IsVeluHom (W : WeierstrassCurve L) (Q : W.toAffine.Point) (N : ℕ)
    (φ : W.toAffine.Point →+ (W.fullKernelQuotient Q N).toAffine.Point) : Prop :=
  φ.ker = AddSubgroup.zmultiples Q ∧
    ∀ P : W.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
      (φ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2))

theorem mem_zmultiples_vcInv_iff (C : VariableChange L) (W : WeierstrassCurve L)
    (Q P : W.toAffine.Point) :
    vcInv C W P ∈ AddSubgroup.zmultiples (vcInv C W Q) ↔ P ∈ AddSubgroup.zmultiples Q := by
  simp only [AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, vcInv_injective C W ?_⟩
    rw [map_zsmul, hm]
  · rintro ⟨m, rfl⟩
    exact ⟨m, (map_zsmul _ _ _).symm⟩

theorem velu_vcInv (C : VariableChange L) (W : WeierstrassCurve L) {N : ℕ}
    (Q : W.toAffine.Point) (hQ : addOrderOf Q = N)
    (φ : W.toAffine.Point →+ (W.fullKernelQuotient Q N).toAffine.Point) (hφ : IsVeluHom W Q N φ)
    (χ : (C • W).toAffine.Point →+ ((C • W).fullKernelQuotient (vcInv C W Q) N).toAffine.Point)
    (hχ : IsVeluHom (C • W) (vcInv C W Q) N χ) (P : W.toAffine.Point) :
    χ (vcInv C W P) =
      castPt (fullKernelQuotient_vcInv C W Q hQ).symm
        (vcInv C (W.fullKernelQuotient Q N) (φ P)) := by
  by_cases hP : P ∈ AddSubgroup.zmultiples Q
  ·
    have h1 : χ (vcInv C W P) = 0 := by
      rw [← AddMonoidHom.mem_ker, hχ.1]; exact (mem_zmultiples_vcInv_iff C W Q P).mpr hP
    have h2 : φ P = 0 := by rw [← AddMonoidHom.mem_ker, hφ.1]; exact hP
    rw [h1, h2, _root_.map_zero, _root_.map_zero]
  · have hP' : vcInv C W P ∉ AddSubgroup.zmultiples (vcInv C W Q) :=
      fun h => hP ((mem_zmultiples_vcInv_iff C W Q P).mp h)
    have hφP : φ P ≠ 0 := by
      intro h; apply hP; rw [← hφ.1, AddMonoidHom.mem_ker]; exact h
    have hL : χ (vcInv C W P) ≠ 0 := by
      intro h; apply hP'; rw [← hχ.1, AddMonoidHom.mem_ker]; exact h
    have hR : castPt (fullKernelQuotient_vcInv C W Q hQ).symm
        (vcInv C (W.fullKernelQuotient Q N) (φ P)) ≠ 0 := by
      intro h
      exact hφP ((vcInv_eq_zero_iff _ _ _).mp ((AddEquiv.map_eq_zero_iff _).mp h))
    apply eq_of_coordsOrZero_eq hL hR
    rw [coordsOrZero_castPt, coordsOrZero_vcInv _ _ _ hφP, hχ.2 _ hP', hφ.2 _ hP,
      vcInvEmbedding_apply]
    have hP0 : P ≠ 0 := fun h => hP (h ▸ zero_mem _)
    have hPk : ∀ k ∈ Finset.Icc 1 (N - 1), P + k • Q ≠ 0 := by
      intro k hk h
      apply hP
      rw [eq_neg_of_add_eq_zero_left h]
      exact neg_mem (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples Q) k)
    have hk0 : ∀ k ∈ Finset.Icc 1 (N - 1), k • Q ≠ 0 := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      exact nsmul_ne_zero_of_mem_Icc hQ hk.1 hk.2

    have hsum1 : ∑ k ∈ Finset.Icc 1 (N - 1),
        ((vcInv C W P + k • vcInv C W Q).coordsOrZero.1 - (k • vcInv C W Q).coordsOrZero.1) =
        ((C.u⁻¹ : Lˣ) : L) ^ 2 * ∑ k ∈ Finset.Icc 1 (N - 1),
          ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [← map_nsmul, ← map_add, coordsOrZero_vcInv _ _ _ (hPk k hk),
        coordsOrZero_vcInv _ _ _ (hk0 k hk), vcInvEmbedding_apply, vcInvEmbedding_apply]
      simp only [vcXInv]
      ring
    have hsum2 : ∑ k ∈ Finset.Icc 1 (N - 1),
        ((vcInv C W P + k • vcInv C W Q).coordsOrZero.2 - (k • vcInv C W Q).coordsOrZero.2) =
        ((C.u⁻¹ : Lˣ) : L) ^ 3 * (∑ k ∈ Finset.Icc 1 (N - 1),
          ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)) -
        ((C.u⁻¹ : Lˣ) : L) ^ 3 * C.s * (∑ k ∈ Finset.Icc 1 (N - 1),
          ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [← map_nsmul, ← map_add, coordsOrZero_vcInv _ _ _ (hPk k hk),
        coordsOrZero_vcInv _ _ _ (hk0 k hk), vcInvEmbedding_apply, vcInvEmbedding_apply]
      simp only [vcYInv]
      ring
    rw [coordsOrZero_vcInv _ _ _ hP0, vcInvEmbedding_apply]
    simp only
    rw [hsum1, hsum2]
    refine Prod.ext ?_ ?_
    · simp only [vcXInv]; ring
    · simp only [vcYInv]; ring

end PointCovariance

section Stabilizing

variable {L : Type*} [Field L] [DecidableEq L]

def autPt {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W) :
    W.toAffine.Point →+ W.toAffine.Point :=
  (castPt hγ).toAddMonoidHom.comp (vcInv γ W)

theorem autPt_apply {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W)
    (P : W.toAffine.Point) : autPt γ hγ P = castPt hγ (vcInv γ W P) := rfl

theorem autPt_injective {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W) :
    Function.Injective (autPt γ hγ) := fun P Q h =>
  vcInv_injective γ W ((castPt hγ).injective h)

theorem autPt_eq_iff_heq {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W)
    (P Q : W.toAffine.Point) :
    autPt γ hγ P = Q ↔ HEq (Point.vcInvFun γ W.toAffine P) Q := by
  rw [autPt_apply, castPt_eq_iff_heq]; rfl

theorem coordsOrZero_autPt {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W)
    (P : W.toAffine.Point) (hP : P ≠ 0) :
    (autPt γ hγ P).coordsOrZero = vcInvEmbedding γ P.coordsOrZero := by
  rw [autPt_apply, coordsOrZero_castPt, coordsOrZero_vcInv _ _ _ hP]

theorem mem_zmultiples_map_iff {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (hf : Function.Injective f) (x y : A) :
    f x ∈ AddSubgroup.zmultiples (f y) ↔ x ∈ AddSubgroup.zmultiples y := by
  simp only [AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, hf (by rw [map_zsmul, hm])⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m, (map_zsmul _ _ _).symm⟩

variable {W : WeierstrassCurve L} {N : ℕ} (γ : VariableChange L) (hγ : γ • W = W)
  {Q : W.toAffine.Point} (hQ : addOrderOf Q = N) (hN : N ≠ 0)
  (hpres : autPt γ hγ Q ∈ AddSubgroup.zmultiples Q)

include hQ in
theorem addOrderOf_autPt : addOrderOf (autPt γ hγ Q) = N := by
  rw [addOrderOf_injective (autPt γ hγ) (autPt_injective γ hγ), hQ]

include hQ hN hpres in

theorem zmultiples_autPt_eq :
    AddSubgroup.zmultiples (autPt γ hγ Q) = AddSubgroup.zmultiples Q := by
  haveI : Finite (AddSubgroup.zmultiples Q) := by
    apply Nat.finite_of_card_ne_zero
    rw [Nat.card_zmultiples, hQ]; exact hN
  apply AddSubgroup.eq_of_le_of_card_ge (AddSubgroup.zmultiples_le_of_mem hpres)
  rw [Nat.card_zmultiples, Nat.card_zmultiples, addOrderOf_autPt γ hγ hQ, hQ]

include hQ hN hpres in

theorem smul_fullKernelQuotient_eq : γ • W.fullKernelQuotient Q N = W.fullKernelQuotient Q N := by
  rw [← fullKernelQuotient_vcInv γ W Q hQ, ← fullKernelQuotient_castPt hγ (vcInv γ W Q) N]
  exact fullKernelQuotient_congr W (addOrderOf_autPt γ hγ hQ) hQ (zmultiples_autPt_eq γ hγ hQ hN hpres)

include hQ hN hpres in

theorem autPt_velu (φ : W.toAffine.Point →+ (W.fullKernelQuotient Q N).toAffine.Point)
    (hφ : IsVeluHom W Q N φ) (P : W.toAffine.Point) :
    autPt γ (smul_fullKernelQuotient_eq γ hγ hQ hN hpres) (φ P) = φ (autPt γ hγ P) := by

  have hord := addOrderOf_autPt γ hγ hQ
  have hzm := zmultiples_autPt_eq γ hγ hQ hN hpres
  have e : W.fullKernelQuotient Q N = (γ • W).fullKernelQuotient (vcInv γ W Q) N :=
    (fullKernelQuotient_congr W hord hQ hzm).symm.trans (fullKernelQuotient_castPt hγ (vcInv γ W Q) N)
  let χ : (γ • W).toAffine.Point →+ ((γ • W).fullKernelQuotient (vcInv γ W Q) N).toAffine.Point :=
    (castPt e).toAddMonoidHom.comp (φ.comp (castPt hγ).toAddMonoidHom)
  have hχapp : ∀ P', χ P' = castPt e (φ (castPt hγ P')) := fun _ => rfl

  have hmem : ∀ P' : (γ • W).toAffine.Point,
      castPt hγ P' ∈ AddSubgroup.zmultiples Q ↔
        P' ∈ AddSubgroup.zmultiples (vcInv γ W Q) := by
    intro P'
    rw [← hzm, autPt_apply]
    exact mem_zmultiples_map_iff (castPt hγ).toAddMonoidHom (castPt hγ).injective P' _
  have hχ : IsVeluHom (γ • W) (vcInv γ W Q) N χ := by
    refine ⟨?_, ?_⟩
    · ext P'
      rw [AddMonoidHom.mem_ker, hχapp, AddEquiv.map_eq_zero_iff, ← AddMonoidHom.mem_ker, hφ.1]
      exact hmem P'
    · intro P' hP'
      have hP₁ : castPt hγ P' ∉ AddSubgroup.zmultiples Q := fun h => hP' ((hmem P').mp h)
      rw [hχapp, coordsOrZero_castPt, hφ.2 _ hP₁, coordsOrZero_castPt]

      have key : ∀ g : W.toAffine.Point → L,
          ∑ k ∈ Finset.Icc 1 (N - 1), (g (castPt hγ P' + k • Q) - g (k • Q)) =
          ∑ k ∈ Finset.Icc 1 (N - 1),
            (g (castPt hγ (P' + k • vcInv γ W Q)) - g (castPt hγ (k • vcInv γ W Q))) := by
        intro g
        rw [sum_nsmul_congr hQ hord hzm.symm (fun T => g (castPt hγ P' + T) - g T)]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [autPt_apply, ← map_nsmul, ← map_add]
      refine Prod.ext ?_ ?_
      · simp only
        rw [key (fun T => T.coordsOrZero.1)]
        simp only [coordsOrZero_castPt]
      · simp only
        rw [key (fun T => T.coordsOrZero.2)]
        simp only [coordsOrZero_castPt]
  have hM := velu_vcInv γ W Q hQ φ hφ χ hχ P
  rw [hχapp] at hM

  have h2 : φ (castPt hγ (vcInv γ W P)) =
      (castPt e).symm (castPt (fullKernelQuotient_vcInv γ W Q hQ).symm
        (vcInv γ (W.fullKernelQuotient Q N) (φ P))) := by
    rw [← hM, AddEquiv.symm_apply_apply]
  rw [autPt_apply γ hγ P, h2, castPt_symm_apply, castPt_castPt]
  rfl

end Stabilizing

section Coord

variable {L : Type*} [Field L]

theorem vcXInv_mul (C C' : VariableChange L) (x : L) :
    vcXInv (C * C') x = vcXInv C (vcXInv C' x) := by
  have hu : (C.u : L) ≠ 0 := C.u.ne_zero
  have hu' : (C'.u : L) ≠ 0 := C'.u.ne_zero
  simp only [vcXInv, VariableChange.mul_def, Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp
  ring

theorem vcYInv_mul (C C' : VariableChange L) (x y : L) :
    vcYInv (C * C') x y = vcYInv C (vcXInv C' x) (vcYInv C' x y) := by
  have hu : (C.u : L) ≠ 0 := C.u.ne_zero
  have hu' : (C'.u : L) ≠ 0 := C'.u.ne_zero
  simp only [vcXInv, vcYInv, VariableChange.mul_def, Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp
  ring

theorem vcXInv_inv (C : VariableChange L) (x : L) : vcXInv C⁻¹ x = vcX C x := by
  have hu : (C.u : L) ≠ 0 := C.u.ne_zero
  simp only [vcXInv, vcX, VariableChange.inv_def, Units.val_inv_eq_inv_val, inv_inv]
  field_simp
  ring

theorem vcYInv_inv (C : VariableChange L) (x y : L) : vcYInv C⁻¹ x y = vcY C x y := by
  have hu : (C.u : L) ≠ 0 := C.u.ne_zero
  simp only [vcYInv, vcY, VariableChange.inv_def, Units.val_inv_eq_inv_val, inv_inv]
  field_simp
  ring

variable [DecidableEq L]

theorem coordsOrZero_vcFun (C : VariableChange L) (W : WeierstrassCurve L)
    (P : (C • W).toAffine.Point) (hP : P ≠ 0) :
    (Point.vcFun C W.toAffine P).coordsOrZero = (vcX C P.coordsOrZero.1, vcY C P.coordsOrZero.1 P.coordsOrZero.2) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · rfl

theorem vcFun_ne_zero (C : VariableChange L) (W : WeierstrassCurve L)
    (P : (C • W).toAffine.Point) (hP : P ≠ 0) : Point.vcFun C W.toAffine P ≠ 0 := by
  intro h
  apply hP
  have := congrArg (vcInv C W) h
  rwa [vcInv_apply, Point.vcFun_leftInverse, _root_.map_zero] at this

theorem autPt_conj {W V : WeierstrassCurve L} (C γ : VariableChange L) (hC : C • W = V)
    (hγ : γ • V = V) (h : (C⁻¹ * γ * C) • W = W) (T : W.toAffine.Point) :
    autPt (C⁻¹ * γ * C) h T =
      Point.equivOfVariableChangeEq (W := W.toAffine) hC
        (autPt γ hγ ((Point.equivOfVariableChangeEq (W := W.toAffine) hC).symm T)) := by
  rcases eq_or_ne T 0 with rfl | hT
  · rw [_root_.map_zero, equivOfVariableChangeEq_symm_apply, _root_.map_zero, _root_.map_zero,
      _root_.map_zero, equivOfVariableChangeEq_apply, _root_.map_zero]
    rfl
  · have h1 : (Point.equivOfVariableChangeEq (W := W.toAffine) hC).symm T ≠ 0 := by
      rw [equivOfVariableChangeEq_symm_apply, Ne, AddEquiv.map_eq_zero_iff, vcInv_eq_zero_iff]
      exact hT
    have h2 : autPt γ hγ ((Point.equivOfVariableChangeEq (W := W.toAffine) hC).symm T) ≠ 0 := by
      intro h'; exact h1 (autPt_injective γ hγ (by rw [h', _root_.map_zero]))
    have h3 : castPt hC.symm
        (autPt γ hγ ((Point.equivOfVariableChangeEq (W := W.toAffine) hC).symm T)) ≠ 0 := by
      rw [Ne, AddEquiv.map_eq_zero_iff]; exact h2
    have hL : autPt (C⁻¹ * γ * C) h T ≠ 0 := fun h' =>
      hT (autPt_injective _ h (by rw [h', _root_.map_zero]))
    have hR : Point.equivOfVariableChangeEq (W := W.toAffine) hC
        (autPt γ hγ ((Point.equivOfVariableChangeEq (W := W.toAffine) hC).symm T)) ≠ 0 := by
      rw [equivOfVariableChangeEq_apply]; exact vcFun_ne_zero C W _ h3
    apply eq_of_coordsOrZero_eq hL hR
    rw [coordsOrZero_autPt _ _ _ hT, equivOfVariableChangeEq_apply, coordsOrZero_vcFun _ _ _ h3,
      coordsOrZero_castPt, coordsOrZero_autPt _ _ _ h1, equivOfVariableChangeEq_symm_apply,
      coordsOrZero_castPt, coordsOrZero_vcInv _ _ _ hT, vcInvEmbedding_apply, vcInvEmbedding_apply,
      vcInvEmbedding_apply]
    simp only
    rw [vcXInv_mul, vcXInv_mul, vcXInv_inv, vcYInv_mul, vcYInv_mul, vcYInv_inv, ← vcXInv_mul]

end Coord

section Count

variable {K : Type*} [Field K] [DecidableEq K]

def StabSet (V : WeierstrassCurve K) (H : AddSubgroup V.toAffine.Point) : Type _ :=
  {γ : VariableChange K // γ • V = V ∧
    ∀ T ∈ H, ∃ T' ∈ H, HEq (Point.vcInvFun γ V.toAffine T) T'}

theorem pres_iff {V : WeierstrassCurve K} (γ : VariableChange K) (hγ : γ • V = V)
    (H : AddSubgroup V.toAffine.Point) :
    (∀ T ∈ H, ∃ T' ∈ H, HEq (Point.vcInvFun γ V.toAffine T) T') ↔ ∀ T ∈ H, autPt γ hγ T ∈ H := by
  refine forall₂_congr fun T _ => ⟨?_, fun h => ⟨_, h, (autPt_eq_iff_heq γ hγ T _).mp rfl⟩⟩
  rintro ⟨T', hT', h⟩
  rwa [(autPt_eq_iff_heq γ hγ T T').mpr h]

theorem finite_stabSet (V : WeierstrassCurve K) [V.IsElliptic] (H : AddSubgroup V.toAffine.Point) :
    Finite (StabSet V H) := by
  haveI := WeierstrassCurve.finite_stabilizer_variableChange K V
  refine Finite.of_injective
    (fun γ : StabSet V H => (⟨γ.1, MulAction.mem_stabilizer_iff.mpr γ.2.1⟩ :
      MulAction.stabilizer (VariableChange K) V)) ?_
  intro a b h
  apply Subtype.ext
  exact congrArg (fun x : MulAction.stabilizer (VariableChange K) V => (x.1 : VariableChange K)) h

def tor (A : Type*) [AddCommGroup A] (N : ℕ) : AddSubgroup A where
  carrier := {P | N • P = 0}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [nsmul_add, ha, hb, add_zero]
  zero_mem' := nsmul_zero N
  neg_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [neg_nsmul, ha, _root_.neg_zero]

theorem mem_tor {A : Type*} [AddCommGroup A] {N : ℕ} {P : A} : P ∈ tor A N ↔ N • P = 0 := Iff.rfl

theorem stab_step {V : WeierstrassCurve K} {N : ℕ} (hN : N ≠ 0) {R : V.toAffine.Point}
    (hR : addOrderOf R = N)
    (χ : V.toAffine.Point →+ (V.fullKernelQuotient R N).toAffine.Point) (hχ : IsVeluHom V R N χ)
    (γ : StabSet V (AddSubgroup.zmultiples R)) :
    ∃ hγ' : γ.1 • V.fullKernelQuotient R N = V.fullKernelQuotient R N,
      ∀ T ∈ (tor _ N).map χ, autPt γ.1 hγ' T ∈ (tor _ N).map χ := by
  have hpres : autPt γ.1 γ.2.1 R ∈ AddSubgroup.zmultiples R :=
    (pres_iff γ.1 γ.2.1 _).mp γ.2.2 R (AddSubgroup.mem_zmultiples R)
  refine ⟨smul_fullKernelQuotient_eq γ.1 γ.2.1 hR hN hpres, ?_⟩
  rintro _ ⟨P, hP, rfl⟩
  rw [autPt_velu γ.1 γ.2.1 hR hN hpres χ hχ P]
  refine ⟨autPt γ.1 γ.2.1 P, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_tor] at hP ⊢
  rw [← map_nsmul, hP, _root_.map_zero]

variable [IsAlgClosed K]

theorem natCard_tor (W : WeierstrassCurve K) [W.IsElliptic] {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0) :
    Nat.card (tor W.toAffine.Point N) = N ^ 2 := by
  obtain ⟨eT⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
    (F := K) (K := K) W hN
  have hb : (W⁄K) = W.toAffine := by
    show (W.baseChange K).toAffine = W.toAffine
    rw [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
  rw [hb] at eT
  have hset : (Submodule.torsionBy ℤ W.toAffine.Point N : Set W.toAffine.Point) =
      (tor W.toAffine.Point N : Set W.toAffine.Point) := by
    ext P
    rw [SetLike.mem_coe, SetLike.mem_coe, Submodule.mem_torsionBy_iff, mem_tor]
    show ((N : ℤ) • P = 0) ↔ N • P = 0
    rw [natCast_zsmul]
  have h1 : Nat.card (Submodule.torsionBy ℤ W.toAffine.Point N) = N ^ 2 := by
    rw [← Nat.card_congr eT.toEquiv, Nat.card_prod, Nat.card_zmod, sq]
  rw [← SetLike.coe_sort_coe, hset] at h1
  exact h1

theorem map_tor_eq_zmultiples {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic] (Q : W.toAffine.Point) (hQ : addOrderOf Q = N)
    (φ : W.toAffine.Point →+ (W.fullKernelQuotient Q N).toAffine.Point) (hφ : IsVeluHom W Q N φ)
    (Q' : (W.fullKernelQuotient Q N).toAffine.Point) (hQ' : addOrderOf Q' = N)
    (hQ'mem : ∀ P : W.toAffine.Point, N • P = 0 → φ P ∈ AddSubgroup.zmultiples Q') :
    (tor W.toAffine.Point N).map φ = AddSubgroup.zmultiples Q' := by
  have hN0 : N ≠ 0 := NeZero.ne N
  have hle : (tor W.toAffine.Point N).map φ ≤ AddSubgroup.zmultiples Q' := by
    rintro _ ⟨P, hP, rfl⟩; exact hQ'mem P hP
  haveI : Finite (AddSubgroup.zmultiples Q') := by
    apply Nat.finite_of_card_ne_zero
    rw [Nat.card_zmultiples, hQ']; exact hN0
  apply AddSubgroup.eq_of_le_of_card_ge hle
  rw [Nat.card_zmultiples, hQ']

  let ψ : tor W.toAffine.Point N →+ (W.fullKernelQuotient Q N).toAffine.Point :=
    φ.comp (tor W.toAffine.Point N).subtype
  have hrange : ψ.range = (tor W.toAffine.Point N).map φ := by
    rw [AddMonoidHom.range_comp, AddSubgroup.range_subtype]
  have hQtor : AddSubgroup.zmultiples Q ≤ tor W.toAffine.Point N := by
    rw [AddSubgroup.zmultiples_le, mem_tor, ← hQ, addOrderOf_nsmul_eq_zero]
  have hker : ψ.ker = (AddSubgroup.zmultiples Q).addSubgroupOf (tor W.toAffine.Point N) := by
    rw [AddSubgroup.addSubgroupOf, ← hφ.1]; rfl
  have hcardker : Nat.card ψ.ker = N := by
    rw [hker, Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hQtor).toEquiv, Nat.card_zmultiples, hQ]
  have hprod := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ψ.ker
  rw [natCard_tor W hN, hcardker, Nat.card_congr (QuotientAddGroup.quotientKerEquivRange ψ).toEquiv,
    hrange, sq] at hprod
  have : Nat.card ((tor W.toAffine.Point N).map φ) = N :=
    (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hN0) hprod).symm
  rw [this]

theorem main {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic] (Q : W.toAffine.Point) (hQ : addOrderOf Q = N)
    (φ : W.toAffine.Point →+ (W.fullKernelQuotient Q N).toAffine.Point) (hφ : IsVeluHom W Q N φ)
    (Q' : (W.fullKernelQuotient Q N).toAffine.Point) (hQ' : addOrderOf Q' = N)
    (hQ'mem : ∀ P : W.toAffine.Point, N • P = 0 → φ P ∈ AddSubgroup.zmultiples Q') :
    Nat.card (StabSet W (AddSubgroup.zmultiples Q)) =
      Nat.card (StabSet (W.fullKernelQuotient Q N) (AddSubgroup.zmultiples Q')) := by
  have hN0 : N ≠ 0 := NeZero.ne N

  have hΔ : (W.fullKernelQuotient Q N).Δ ≠ 0 :=
    WeierstrassCurve.fullKernelQuotient_discriminant_ne_zero N W hN Q hQ
  haveI hE' : (W.fullKernelQuotient Q N).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  have hΔ' : ((W.fullKernelQuotient Q N).fullKernelQuotient Q' N).Δ ≠ 0 :=
    WeierstrassCurve.fullKernelQuotient_discriminant_ne_zero N _ hN Q' hQ'
  haveI hE'' : ((W.fullKernelQuotient Q N).fullKernelQuotient Q' N).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr hΔ'⟩

  obtain ⟨φ', hφ'ker, hφ'⟩ := WeierstrassCurve.exists_fullKernelHom (W.fullKernelQuotient Q N) hN Q' hQ'
  have hφ'V : IsVeluHom _ Q' N φ' := ⟨hφ'ker, hφ'⟩
  obtain ⟨C, hC, hbi⟩ :=
    WeierstrassCurve.exists_variableChange_eq_fullKernelQuotient_fullKernelQuotient_comp_eq_smul
      hN W Q hQ hΔ φ hφ.1 hφ.2 Q' hQ' hQ'mem hΔ' φ' hφ'ker hφ'

  let ε := Point.equivOfVariableChangeEq (W := W.toAffine) hC
  have himg : (tor W.toAffine.Point N).map φ = AddSubgroup.zmultiples Q' :=
    map_tor_eq_zmultiples hN W Q hQ φ hφ Q' hQ' hQ'mem
  let H₂ : AddSubgroup ((W.fullKernelQuotient Q N).fullKernelQuotient Q' N).toAffine.Point :=
    (tor (W.fullKernelQuotient Q N).toAffine.Point N).map φ'

  have hH₂ : ∀ T : W.toAffine.Point, T ∈ AddSubgroup.zmultiples Q ↔ ε.symm T ∈ H₂ := by
    intro T
    constructor
    · intro hT
      obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hT
      obtain ⟨Q₀, hQ₀⟩ := WeierstrassCurve.exists_nsmul_eq_of_isAlgClosed W N hN Q
      have hR : φ (m • Q₀) ∈ tor (W.fullKernelQuotient Q N).toAffine.Point N := by
        rw [mem_tor, ← map_nsmul, smul_comm, hQ₀, ← AddMonoidHom.mem_ker, hφ.1]
        exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples Q) m
      have hval : ε (φ' (φ (m • Q₀))) = m • Q := by
        show Point.equivOfVariableChangeEq (W := W.toAffine) hC (φ' (φ (m • Q₀))) = m • Q
        rw [hbi, smul_comm, natCast_zsmul, hQ₀]
      rw [← hval, Equiv.symm_apply_apply]
      exact ⟨_, hR, rfl⟩
    · rintro ⟨R, hR, hRT⟩
      obtain ⟨P, rfl⟩ :=
        WeierstrassCurve.fullKernelHom_surjective_of_isAlgClosed W hN Q hQ φ hφ.1 hφ.2 R
      have hT : T = ε (φ' (φ P)) := by rw [hRT, Equiv.apply_symm_apply]
      rw [hT]
      show Point.equivOfVariableChangeEq (W := W.toAffine) hC (φ' (φ P)) ∈ _
      rw [hbi, natCast_zsmul, ← hφ.1, AddMonoidHom.mem_ker, map_nsmul]
      rw [SetLike.mem_coe, mem_tor] at hR
      exact hR

  let S₀ := StabSet W (AddSubgroup.zmultiples Q)
  let S₁ := StabSet (W.fullKernelQuotient Q N) (AddSubgroup.zmultiples Q')
  let S₂ := StabSet ((W.fullKernelQuotient Q N).fullKernelQuotient Q' N) H₂
  haveI : Finite S₀ := finite_stabSet W _
  haveI : Finite S₁ := finite_stabSet (W.fullKernelQuotient Q N) _
  haveI : Finite S₂ := finite_stabSet ((W.fullKernelQuotient Q N).fullKernelQuotient Q' N) _
  let ι₁ : S₀ → S₁ := fun γ => ⟨γ.1, by
    obtain ⟨hγ', h⟩ := stab_step hN0 hQ φ hφ γ
    refine ⟨hγ', (pres_iff γ.1 hγ' _).mpr ?_⟩
    rw [← himg]; exact h⟩
  let ι₂ : S₁ → S₂ := fun γ => ⟨γ.1, by
    obtain ⟨hγ', h⟩ := stab_step hN0 hQ' φ' hφ'V γ
    exact ⟨hγ', (pres_iff γ.1 hγ' _).mpr h⟩⟩
  have hconj : ∀ γ : S₂, (C⁻¹ * γ.1 * C) • W = W := by
    intro γ
    rw [mul_smul, mul_smul, hC, γ.2.1, ← hC, inv_smul_smul]
  let ι₃ : S₂ → S₀ := fun γ => ⟨C⁻¹ * γ.1 * C, hconj γ, by
    refine (pres_iff _ (hconj γ) _).mpr fun T hT => ?_
    rw [autPt_conj C γ.1 hC γ.2.1 (hconj γ) T, hH₂]
    show ε.symm (ε _) ∈ H₂
    rw [Equiv.symm_apply_apply]
    exact (pres_iff γ.1 γ.2.1 H₂).mp γ.2.2 _ ((hH₂ T).mp hT)⟩
  have i₁ : Function.Injective ι₁ := fun a b h => Subtype.ext (congrArg (fun x : S₁ => x.1) h)
  have i₂ : Function.Injective ι₂ := fun a b h => Subtype.ext (congrArg (fun x : S₂ => x.1) h)
  have i₃ : Function.Injective ι₃ := by
    intro a b h
    have h' : C⁻¹ * a.1 * C = C⁻¹ * b.1 * C := congrArg (fun x : S₀ => x.1) h
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h'))
  have h01 := Nat.card_le_card_of_injective ι₁ i₁
  have h12 := Nat.card_le_card_of_injective ι₂ i₂
  have h20 := Nat.card_le_card_of_injective ι₃ i₃
  exact le_antisymm h01 (h12.trans h20)

end Count

end P2MKcStabDual

end

open WeierstrassCurve WeierstrassCurve.Affine in
theorem solution
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic]
    (Q : W.toAffine.Point) (hQ : addOrderOf Q = N)
    (φ : W.toAffine.Point →+ (W.fullKernelQuotient Q N).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ P : W.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
      (φ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)))
    (Q' : (W.fullKernelQuotient Q N).toAffine.Point) (hQ' : addOrderOf Q' = N)
    (hQ'mem : ∀ P : W.toAffine.Point, N • P = 0 → φ P ∈ AddSubgroup.zmultiples Q') :
    Nat.card {γ : VariableChange K // γ • W = W ∧
        ∀ T ∈ AddSubgroup.zmultiples Q, ∃ T' ∈ AddSubgroup.zmultiples Q,
          HEq (Point.vcInvFun γ W.toAffine T) T'} =
      Nat.card {γ : VariableChange K //
        γ • W.fullKernelQuotient Q N = W.fullKernelQuotient Q N ∧
        ∀ T ∈ AddSubgroup.zmultiples Q', ∃ T' ∈ AddSubgroup.zmultiples Q',
          HEq (Point.vcInvFun γ (W.fullKernelQuotient Q N).toAffine T) T'} :=
  P2MKcStabDual.main hN W Q hQ φ ⟨hφker, hφ⟩ Q' hQ' hQ'mem

end S_WeierstrassCurve_natCard_stabilizer_zmultiples_eq_natCard_stabilizer_zmultiples_fullKernelQuotient
end P2MW
export P2MW.S_WeierstrassCurve_natCard_stabilizer_zmultiples_eq_natCard_stabilizer_zmultiples_fullKernelQuotient (solution)
