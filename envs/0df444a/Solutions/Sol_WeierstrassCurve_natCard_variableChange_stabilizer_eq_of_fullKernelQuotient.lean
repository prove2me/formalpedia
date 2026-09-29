-- Prove2me | solution 1 for WeierstrassCurve.natCard_variableChange_stabilizer_eq_of_fullKernelQuotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/f025bc81-5da1-5963-852d-66e36ea00aa2

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_WeierstrassCurve_VeluVariableChange
import Theorems.Thm_WeierstrassCurve_variableChange_veluQuotientOfSums_asymWeights
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_variableChange_eq_fullKernelQuotient_fullKernelQuotient_comp_eq_smul
import Theorems.Thm_WeierstrassCurve_fullKernelQuotient_discriminant_ne_zero
import Theorems.Thm_WeierstrassCurve_exists_fullKernelHom
import Theorems.Thm_WeierstrassCurve_fullKernelHom_surjective_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_natCard_variableChange_stabilizer_eq_of_fullKernelQuotient
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsDiscreteValuationRingSubtypeFunctionFieldMemValuationSubringValuationSubringWithZeroMultiplicativeIntValuationInfty WeierstrassCurve.Affine.valuationInfty_isNontrivial WeierstrassCurve.veluQuotient2_isShortNF WeierstrassCurve.instIsShortNFMk"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"
set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace StabDual

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [DecidableEq K]

theorem coordsOrZero_eq_of_heq {V V' : WeierstrassCurve K} (h : V = V')
    (P : V.toAffine.Point) (P' : V'.toAffine.Point) (hP : HEq P P') :
    P.coordsOrZero = P'.coordsOrZero := by
  subst h
  rw [eq_of_heq hP]

theorem ne_zero_of_heq {V V' : WeierstrassCurve K} (h : V = V')
    (P : V.toAffine.Point) (P' : V'.toAffine.Point) (hP : HEq P P') (h0 : P ≠ 0) : P' ≠ 0 := by
  subst h
  rw [← eq_of_heq hP]; exact h0

theorem vcInvEmbedding_coordsOrZero (C : VariableChange K) (W : WeierstrassCurve K)
    (P : W.toAffine.Point) (hP : P ≠ 0) :
    vcInvEmbedding C P.coordsOrZero = (Point.vcInvFun C W.toAffine P).coordsOrZero := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · rfl

theorem vcInvFun_ne_zero (C : VariableChange K) (W : WeierstrassCurve K)
    (P : W.toAffine.Point) (hP : P ≠ 0) : Point.vcInvFun C W.toAffine P ≠ 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · exact fun h' => by cases h'

theorem negY_mem_summingSet (W : WeierstrassCurve K) (Q : W.toAffine.Point) (N : ℕ) (hQ : addOrderOf Q = N)
    (hN : 0 < N) {P : K × K} (hP : P ∈ W.oddOrderSummingSet Q (N - 1)) :
    (P.1, W.toAffine.negY P.1 P.2) ∈ W.oddOrderSummingSet Q (N - 1) := by
  rw [mem_oddOrderSummingSet] at hP ⊢
  obtain ⟨k, hk1, hkN, rfl⟩ := hP
  refine ⟨N - k, by omega, by omega, ?_⟩
  have hk0 : (k • Q) ≠ 0 := by
    intro h
    have := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h
    rw [hQ] at this
    exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  have hneg : (N - k) • Q = -(k • Q) := by
    rw [eq_neg_iff_add_eq_zero, ← add_nsmul, Nat.sub_add_cancel (by omega), ← hQ, addOrderOf_nsmul_eq_zero]
  rw [hneg]
  rcases hkQ : k • Q with _ | ⟨x, y, h⟩
  · exact absurd hkQ hk0
  · rfl

theorem coordsOrZero_mem_summingSet (W : WeierstrassCurve K) (Q : W.toAffine.Point) (N : ℕ) (hQ : addOrderOf Q = N)
    (hN : 0 < N) {T : W.toAffine.Point} (hT : T ∈ AddSubgroup.zmultiples Q) (hT0 : T ≠ 0) :
    T.coordsOrZero ∈ W.oddOrderSummingSet Q (N - 1) := by
  rw [mem_oddOrderSummingSet]
  obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hT

  have hper : ∀ w : ℤ, w • Q = (w % N) • Q := fun w => by
    conv_lhs => rw [← Int.emod_add_mul_ediv w N, add_zsmul, mul_comm, mul_zsmul, natCast_zsmul]
    rw [← hQ, addOrderOf_nsmul_eq_zero, zsmul_zero, add_zero]
  set k := (z % N).toNat with hk
  have hz : z % N = (k : ℤ) := (Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hN.ne'))).symm
  have hkQ : z • Q = k • Q := by rw [hper z, hz, natCast_zsmul]
  refine ⟨k, ?_, ?_, by rw [hkQ]⟩
  · by_contra h
    have : k = 0 := by omega
    rw [hkQ, this, zero_nsmul] at hT0; exact hT0 rfl
  · have : (k : ℤ) < N := hz ▸ Int.emod_lt_of_pos _ (by exact_mod_cast hN)
    omega

theorem smul_fullKernelQuotient_eq (γ : VariableChange K) (W : WeierstrassCurve K) (hγ : γ • W = W)
    (Q : W.toAffine.Point) (N : ℕ) (hQ : addOrderOf Q = N) (hN : 0 < N)
    (hstab : ∀ T ∈ AddSubgroup.zmultiples Q, ∃ T' ∈ AddSubgroup.zmultiples Q,
      HEq (Point.vcInvFun γ W.toAffine T) T') :
    γ • W.fullKernelQuotient Q N = W.fullKernelQuotient Q N := by
  set S := W.oddOrderSummingSet Q (N - 1) with hS

  have hmapS : S.map (vcInvEmbedding γ) = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro P hP
      rw [Finset.mem_map] at hP
      obtain ⟨P₀, hP₀, rfl⟩ := hP
      rw [hS, mem_oddOrderSummingSet] at hP₀
      obtain ⟨k, hk1, hkN, rfl⟩ := hP₀
      have hk0 : (k • Q) ≠ 0 := by
        intro h
        have := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h
        rw [hQ] at this
        exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
      obtain ⟨T', hT', hheq⟩ := hstab (k • Q) ((AddSubgroup.zmultiples Q).nsmul_mem (AddSubgroup.mem_zmultiples Q) k)
      rw [vcInvEmbedding_coordsOrZero γ W _ hk0,
        coordsOrZero_eq_of_heq hγ _ _ hheq]
      exact coordsOrZero_mem_summingSet W Q N hQ hN hT'
        (ne_zero_of_heq hγ _ _ hheq (vcInvFun_ne_zero γ W _ hk0))
    · rw [Finset.card_map]

  have hneg : ∀ P ∈ S, (P.1, W.toAffine.negY P.1 P.2) ∈ S := fun P hP => negY_mem_summingSet W Q N hQ hN hP
  have key := variableChange_veluQuotientOfSums_asymWeights γ W S hneg
  rw [hmapS] at key

  have aux : ∀ (V : WeierstrassCurve K), γ • W = V →
      V.veluQuotientOfSums (∑ P ∈ S, V.veluGx P.1 P.2)
        (∑ P ∈ S, (P.1 * V.veluGx P.1 P.2 - P.2 * V.veluGy P.1 P.2))
        = γ • W.veluQuotientOfSums (∑ P ∈ S, W.veluGx P.1 P.2)
          (∑ P ∈ S, (P.1 * W.veluGx P.1 P.2 - P.2 * W.veluGy P.1 P.2)) := by
    intro V hV; subst hV; exact key
  have := aux W hγ
  unfold fullKernelQuotient
  exact this.symm

def castPt {V V' : WeierstrassCurve K} (h : V = V') : V.toAffine.Point ≃+ V'.toAffine.Point := by
  subst h; exact AddEquiv.refl _

theorem heq_castPt {V V' : WeierstrassCurve K} (h : V = V') (P : V.toAffine.Point) : HEq P (castPt h P) := by
  subst h; rfl

theorem castPt_eq_iff_heq {V V' : WeierstrassCurve K} (h : V = V') (P : V.toAffine.Point) (P' : V'.toAffine.Point) :
    castPt h P = P' ↔ HEq P P' := by
  subst h; simp [castPt]

theorem coordsOrZero_castPt {V V' : WeierstrassCurve K} (h : V = V') (P : V.toAffine.Point) :
    (castPt h P).coordsOrZero = P.coordsOrZero := by
  subst h; rfl

noncomputable def vcInvHom (C : VariableChange K) (W : WeierstrassCurve K) :
    W.toAffine.Point →+ (C • W).toAffine.Point :=
  { toFun := Point.vcInvFun C W.toAffine
    map_zero' := Point.vcInvFun_zero
    map_add' := Point.vcInvFun_add C W.toAffine }

@[scoped simp] theorem vcInvHom_apply (C : VariableChange K) (W : WeierstrassCurve K) (P : W.toAffine.Point) :
    vcInvHom C W P = Point.vcInvFun C W.toAffine P := rfl

theorem vcInvFun_injective (C : VariableChange K) (W : WeierstrassCurve K) :
    Function.Injective (Point.vcInvFun C W.toAffine) :=
  (Point.vcFun_rightInverse (C := C) (W := W.toAffine)).injective

noncomputable def autPt (γ : VariableChange K) (W : WeierstrassCurve K) (hγ : γ • W = W) :
    W.toAffine.Point →+ W.toAffine.Point :=
  (castPt hγ).toAddMonoidHom.comp (vcInvHom γ W)

theorem autPt_apply (γ : VariableChange K) (W : WeierstrassCurve K) (hγ : γ • W = W) (P : W.toAffine.Point) :
    autPt γ W hγ P = castPt hγ (Point.vcInvFun γ W.toAffine P) := rfl

theorem autPt_injective (γ : VariableChange K) (W : WeierstrassCurve K) (hγ : γ • W = W) :
    Function.Injective (autPt γ W hγ) :=
  (castPt hγ).injective.comp (vcInvFun_injective γ W)

theorem autPt_ne_zero (γ : VariableChange K) (W : WeierstrassCurve K) (hγ : γ • W = W) {P : W.toAffine.Point}
    (hP : P ≠ 0) : autPt γ W hγ P ≠ 0 := fun h =>
  hP (autPt_injective γ W hγ (by rw [h, map_zero]))

theorem coordsOrZero_autPt (γ : VariableChange K) (W : WeierstrassCurve K) (hγ : γ • W = W) {P : W.toAffine.Point}
    (hP : P ≠ 0) : (autPt γ W hγ P).coordsOrZero = vcInvEmbedding γ P.coordsOrZero := by
  rw [autPt_apply, coordsOrZero_castPt, vcInvEmbedding_coordsOrZero γ W P hP]

theorem autPt_mem_zmultiples (γ : VariableChange K) (W : WeierstrassCurve K) (hγ : γ • W = W) (Q : W.toAffine.Point)
    (hstab : ∀ T ∈ AddSubgroup.zmultiples Q, ∃ T' ∈ AddSubgroup.zmultiples Q,
      HEq (Point.vcInvFun γ W.toAffine T) T')
    {T : W.toAffine.Point} (hT : T ∈ AddSubgroup.zmultiples Q) : autPt γ W hγ T ∈ AddSubgroup.zmultiples Q := by
  obtain ⟨T', hT', hheq⟩ := hstab T hT
  rw [autPt_apply, (castPt_eq_iff_heq hγ _ _).mpr hheq]
  exact hT'

theorem autPt_surjOn_zmultiples (γ : VariableChange K) (W : WeierstrassCurve K) (hγ : γ • W = W) (Q : W.toAffine.Point)
    (N : ℕ) (hQ : addOrderOf Q = N) (hN : 0 < N)
    (hstab : ∀ T ∈ AddSubgroup.zmultiples Q, ∃ T' ∈ AddSubgroup.zmultiples Q,
      HEq (Point.vcInvFun γ W.toAffine T) T')
    {T : W.toAffine.Point} (hT : T ∈ AddSubgroup.zmultiples Q) :
    ∃ T₀ ∈ AddSubgroup.zmultiples Q, autPt γ W hγ T₀ = T := by
  classical
  have hfin : IsOfFinAddOrder Q := addOrderOf_pos_iff.mp (hQ ▸ hN)
  haveI : Finite (AddSubgroup.zmultiples Q) := hfin.finite_zmultiples
  let g : AddSubgroup.zmultiples Q → AddSubgroup.zmultiples Q :=
    fun T => ⟨autPt γ W hγ T.1, autPt_mem_zmultiples γ W hγ Q hstab T.2⟩
  have hg : Function.Injective g := by
    intro a b h
    exact Subtype.ext (autPt_injective γ W hγ (congrArg Subtype.val h))
  obtain ⟨⟨T₀, hT₀⟩, h⟩ := (Finite.injective_iff_surjective.mp hg) ⟨T, hT⟩
  exact ⟨T₀, hT₀, congrArg Subtype.val h⟩

theorem not_mem_zmultiples_of_autPt (γ : VariableChange K) (W : WeierstrassCurve K) (hγ : γ • W = W) (Q : W.toAffine.Point)
    (N : ℕ) (hQ : addOrderOf Q = N) (hN : 0 < N)
    (hstab : ∀ T ∈ AddSubgroup.zmultiples Q, ∃ T' ∈ AddSubgroup.zmultiples Q,
      HEq (Point.vcInvFun γ W.toAffine T) T')
    {P : W.toAffine.Point} (hP : P ∉ AddSubgroup.zmultiples Q) : autPt γ W hγ P ∉ AddSubgroup.zmultiples Q := by
  intro h
  obtain ⟨T₀, hT₀, he⟩ := autPt_surjOn_zmultiples γ W hγ Q N hQ hN hstab h
  exact hP ((autPt_injective γ W hγ he) ▸ hT₀)

section F2b

variable (γ : VariableChange K) (W : WeierstrassCurve K) (hγ : γ • W = W)
  (Q : W.toAffine.Point) (N : ℕ) (hQ : addOrderOf Q = N) (hN : 0 < N)
  (hstab : ∀ T ∈ AddSubgroup.zmultiples Q, ∃ T' ∈ AddSubgroup.zmultiples Q,
    HEq (Point.vcInvFun γ W.toAffine T) T')

include hQ hN in

theorem exists_eq_nsmul_of_mem_zmultiples {T : W.toAffine.Point} (hT : T ∈ AddSubgroup.zmultiples Q) (hT0 : T ≠ 0) :
    ∃ k, 1 ≤ k ∧ k ≤ N - 1 ∧ k • Q = T := by
  obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hT
  have hper : ∀ w : ℤ, w • Q = (w % N) • Q := fun w => by
    conv_lhs => rw [← Int.emod_add_mul_ediv w N, add_zsmul, mul_comm, mul_zsmul, natCast_zsmul]
    rw [← hQ, addOrderOf_nsmul_eq_zero, zsmul_zero, add_zero]
  set k := (z % N).toNat with hk
  have hz : z % N = (k : ℤ) := (Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hN.ne'))).symm
  have hkQ : z • Q = k • Q := by rw [hper z, hz, natCast_zsmul]
  refine ⟨k, ?_, ?_, hkQ.symm⟩
  · by_contra h
    have : k = 0 := by omega
    rw [hkQ, this, zero_nsmul] at hT0; exact hT0 rfl
  · have : (k : ℤ) < N := hz ▸ Int.emod_lt_of_pos _ (by exact_mod_cast hN)
    omega

include hQ hN in
theorem nsmul_ne_zero {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N - 1) : k • Q ≠ 0 := by
  intro h
  have := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h
  rw [hQ] at this
  exact absurd (Nat.le_of_dvd (by omega) this) (by omega)

include hQ hN in
theorem nsmul_injOn : Set.InjOn (fun k : ℕ => k • Q) (Finset.Icc 1 (N - 1) : Set ℕ) := by
  intro a ha b hb h
  simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
  simp only at h

  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have h0 : (b - a) • Q = 0 := by
      have : b • Q = (b - a) • Q + a • Q := by rw [← add_nsmul, Nat.sub_add_cancel hlt.le]
      rw [this] at h
      simpa using h.symm
    exact nsmul_ne_zero W Q N hQ hN (k := b - a) (by omega) (by omega) h0
  · have h0 : (a - b) • Q = 0 := by
      have : a • Q = (a - b) • Q + b • Q := by rw [← add_nsmul, Nat.sub_add_cancel hlt.le]
      rw [this] at h
      simpa using h
    exact nsmul_ne_zero W Q N hQ hN (k := a - b) (by omega) (by omega) h0

include hQ hN hstab in

theorem sum_comp_autPt_nsmul {M : Type*} [AddCommMonoid M] (g : W.toAffine.Point → M) :
    ∑ k ∈ Finset.Icc 1 (N - 1), g (autPt γ W hγ (k • Q)) = ∑ k ∈ Finset.Icc 1 (N - 1), g (k • Q) := by
  classical
  set I := Finset.Icc 1 (N - 1)
  set T : Finset W.toAffine.Point := I.image (fun k : ℕ => k • Q) with hT
  have hinj := nsmul_injOn W Q N hQ hN
  have h1 : ∑ k ∈ I, g (k • Q) = ∑ P ∈ T, g P := (Finset.sum_image hinj).symm
  have h2 : ∑ k ∈ I, g (autPt γ W hγ (k • Q)) = ∑ P ∈ T, g (autPt γ W hγ P) :=
    (Finset.sum_image (f := fun P => g (autPt γ W hγ P)) hinj).symm
  have h3 : ∑ P ∈ T, g (autPt γ W hγ P) = ∑ P ∈ T.image (autPt γ W hγ), g P :=
    (Finset.sum_image ((autPt_injective γ W hγ).injOn)).symm
  have h4 : T.image (autPt γ W hγ) = T := by
    apply Finset.eq_of_subset_of_card_le
    · intro P hP
      rw [Finset.mem_image] at hP
      obtain ⟨P₀, hP₀, rfl⟩ := hP
      rw [hT, Finset.mem_image] at hP₀
      obtain ⟨k, hk, rfl⟩ := hP₀
      rw [Finset.mem_Icc] at hk
      have hmem : autPt γ W hγ (k • Q) ∈ AddSubgroup.zmultiples Q :=
        autPt_mem_zmultiples γ W hγ Q hstab ((AddSubgroup.zmultiples Q).nsmul_mem (AddSubgroup.mem_zmultiples Q) k)
      have hne : autPt γ W hγ (k • Q) ≠ 0 := autPt_ne_zero γ W hγ (nsmul_ne_zero W Q N hQ hN hk.1 hk.2)
      obtain ⟨k', hk'1, hk'N, hk'⟩ := exists_eq_nsmul_of_mem_zmultiples W Q N hQ hN hmem hne
      rw [hT, Finset.mem_image]
      exact ⟨k', Finset.mem_Icc.mpr ⟨hk'1, hk'N⟩, hk'⟩
    · rw [Finset.card_image_of_injective _ (autPt_injective γ W hγ)]
  rw [h2, h3, h4, ← h1]

theorem vcXInv_add_sum {ι : Type*} (I : Finset ι) (a : K) (b c : ι → K) :
    vcXInv γ (a + ∑ i ∈ I, (b i - c i)) = vcXInv γ a + ∑ i ∈ I, (vcXInv γ (b i) - vcXInv γ (c i)) := by
  have hterm : ∀ i, vcXInv γ (b i) - vcXInv γ (c i) = ((γ.u⁻¹ : Kˣ) : K) ^ 2 * (b i - c i) := fun i => by
    simp only [vcXInv]; ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum]
  simp only [vcXInv]
  ring

theorem vcYInv_add_sum {ι : Type*} (I : Finset ι) (a a' : K) (xb xc yb yc : ι → K) :
    vcYInv γ (a + ∑ i ∈ I, (xb i - xc i)) (a' + ∑ i ∈ I, (yb i - yc i))
      = vcYInv γ a a' + ∑ i ∈ I, (vcYInv γ (xb i) (yb i) - vcYInv γ (xc i) (yc i)) := by
  have hterm : ∀ i, vcYInv γ (xb i) (yb i) - vcYInv γ (xc i) (yc i)
      = ((γ.u⁻¹ : Kˣ) : K) ^ 3 * ((yb i - yc i) - γ.s * (xb i - xc i)) := fun i => by
    simp only [vcYInv]; ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum]
  have hsplit : ∑ i ∈ I, (yb i - yc i - γ.s * (xb i - xc i))
      = ∑ i ∈ I, (yb i - yc i) - γ.s * ∑ i ∈ I, (xb i - xc i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hsplit]
  simp only [vcYInv]
  ring

include hQ hN hstab in

theorem autPt_velu_comm
    (φ : W.toAffine.Point →+ (W.fullKernelQuotient Q N).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ P : W.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
      (φ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)))
    (P : W.toAffine.Point) :
    autPt γ (W.fullKernelQuotient Q N) (smul_fullKernelQuotient_eq γ W hγ Q N hQ hN hstab) (φ P)
      = φ (autPt γ W hγ P) := by
  set hW' := smul_fullKernelQuotient_eq γ W hγ Q N hQ hN hstab
  by_cases hP : P ∈ AddSubgroup.zmultiples Q
  · have h1 : φ P = 0 := by rw [← AddMonoidHom.mem_ker, hφker]; exact hP
    have h2 : φ (autPt γ W hγ P) = 0 := by
      rw [← AddMonoidHom.mem_ker, hφker]; exact autPt_mem_zmultiples γ W hγ Q hstab hP
    rw [h1, h2, map_zero]
  · have hP0 : P ≠ 0 := fun h => hP (h ▸ zero_mem _)
    have hγP : autPt γ W hγ P ∉ AddSubgroup.zmultiples Q := not_mem_zmultiples_of_autPt γ W hγ Q N hQ hN hstab hP
    have hφP0 : φ P ≠ 0 := fun h => hP (by rw [← hφker, AddMonoidHom.mem_ker]; exact h)
    have hφγP0 : φ (autPt γ W hγ P) ≠ 0 := fun h => hγP (by rw [← hφker, AddMonoidHom.mem_ker]; exact h)
    apply eq_of_coordsOrZero_eq (autPt_ne_zero γ _ hW' hφP0) hφγP0
    rw [coordsOrZero_autPt γ _ hW' hφP0, hφ P hP, hφ (autPt γ W hγ P) hγP, vcInvEmbedding_apply,
      coordsOrZero_autPt γ W hγ hP0, vcInvEmbedding_apply]

    have hk0 : ∀ k ∈ Finset.Icc 1 (N - 1), k • Q ≠ 0 := fun k hk =>
      nsmul_ne_zero W Q N hQ hN (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
    have hPk0 : ∀ k : ℕ, P + k • Q ≠ 0 := fun k h => hP (by
      have : P = -(k • Q) := eq_neg_of_add_eq_zero_left h
      rw [this]; exact neg_mem ((AddSubgroup.zmultiples Q).nsmul_mem (AddSubgroup.mem_zmultiples Q) k))

    have hx : ∑ k ∈ Finset.Icc 1 (N - 1),
          ((autPt γ W hγ P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1)
        = ∑ k ∈ Finset.Icc 1 (N - 1),
          (vcXInv γ (P + k • Q).coordsOrZero.1 - vcXInv γ (k • Q).coordsOrZero.1) := by
      rw [← sum_comp_autPt_nsmul γ W hγ Q N hQ hN hstab
        (fun T => (autPt γ W hγ P + T).coordsOrZero.1 - T.coordsOrZero.1)]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [← map_add, coordsOrZero_autPt γ W hγ (hPk0 k), coordsOrZero_autPt γ W hγ (hk0 k hk),
        vcInvEmbedding_apply, vcInvEmbedding_apply]
    have hy : ∑ k ∈ Finset.Icc 1 (N - 1),
          ((autPt γ W hγ P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)
        = ∑ k ∈ Finset.Icc 1 (N - 1),
          (vcYInv γ (P + k • Q).coordsOrZero.1 (P + k • Q).coordsOrZero.2
            - vcYInv γ (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2) := by
      rw [← sum_comp_autPt_nsmul γ W hγ Q N hQ hN hstab
        (fun T => (autPt γ W hγ P + T).coordsOrZero.2 - T.coordsOrZero.2)]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [← map_add, coordsOrZero_autPt γ W hγ (hPk0 k), coordsOrZero_autPt γ W hγ (hk0 k hk),
        vcInvEmbedding_apply, vcInvEmbedding_apply]
    rw [hx, hy, vcXInv_add_sum, vcYInv_add_sum]

include hγ hQ hN hstab in

theorem mem_stab_quotient (φ : W.toAffine.Point →+ (W.fullKernelQuotient Q N).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ P : W.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
      (φ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2))) :
    γ • W.fullKernelQuotient Q N = W.fullKernelQuotient Q N ∧
      ∀ P : W.toAffine.Point, N • P = 0 → ∃ P' : W.toAffine.Point, N • P' = 0 ∧
        HEq (Point.vcInvFun γ (W.fullKernelQuotient Q N).toAffine (φ P)) (φ P') := by
  refine ⟨smul_fullKernelQuotient_eq γ W hγ Q N hQ hN hstab, fun P hP => ⟨autPt γ W hγ P, ?_, ?_⟩⟩
  · rw [← map_nsmul, hP, map_zero]
  · rw [← castPt_eq_iff_heq (smul_fullKernelQuotient_eq γ W hγ Q N hQ hN hstab)]
    exact autPt_velu_comm γ W hγ Q N hQ hN hstab φ hφker hφ P

end F2b

theorem exists_bezout_of_addOrderOf_eq {N : ℕ} [NeZero N] (a b : ZMod N) (hv : addOrderOf ((a, b) : ZMod N × ZMod N) = N) :
    ∃ x y : ZMod N, x * a + y * b = 1 := by

  set d := Nat.gcd (Nat.gcd a.val b.val) N with hd
  have hdN : d ∣ N := Nat.gcd_dvd_right _ _
  have hda : d ∣ a.val := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  have hdb : d ∣ b.val := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have hdpos : 0 < d := Nat.pos_of_ne_zero fun h => by
    rw [h] at hdN; exact NeZero.ne N (zero_dvd_iff.mp hdN)
  have hkill : (N / d) • ((a, b) : ZMod N × ZMod N) = 0 := by
    obtain ⟨a', ha'⟩ := hda; obtain ⟨b', hb'⟩ := hdb; obtain ⟨n', hn'⟩ := hdN
    have hNd : N / d = n' := by rw [hn', Nat.mul_div_cancel_left _ hdpos]
    ext
    · show (N / d) • a = 0
      rw [← ZMod.natCast_zmod_val a, ha', hNd, nsmul_eq_mul, ← Nat.cast_mul,
        show n' * (d * a') = N * a' by rw [hn']; ring, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    · show (N / d) • b = 0
      rw [← ZMod.natCast_zmod_val b, hb', hNd, nsmul_eq_mul, ← Nat.cast_mul,
        show n' * (d * b') = N * b' by rw [hn']; ring, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have hdvd : N ∣ N / d := by
    have := addOrderOf_dvd_of_nsmul_eq_zero hkill
    rwa [hv] at this
  have hd1 : d = 1 := by
    obtain ⟨n', hn'⟩ := hdN
    have hNd : N / d = n' := by rw [hn', Nat.mul_div_cancel_left _ hdpos]
    rw [hNd] at hdvd
    have hn'pos : 0 < n' := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hn'; exact NeZero.ne N hn'
    have := Nat.le_of_dvd hn'pos hdvd
    rw [hn'] at this
    nlinarith

  have h1 : (Nat.gcd (Nat.gcd a.val b.val) N : ℤ) = 1 := by rw [← hd, hd1]; rfl
  have hg1 := Nat.gcd_eq_gcd_ab (Nat.gcd a.val b.val) N
  have hg2 := Nat.gcd_eq_gcd_ab a.val b.val
  set g := Nat.gcd a.val b.val
  refine ⟨((Nat.gcdA a.val b.val * Nat.gcdA g N : ℤ) : ZMod N), ((Nat.gcdB a.val b.val * Nat.gcdA g N : ℤ) : ZMod N), ?_⟩
  have key : ((a.val : ℤ) * Nat.gcdA a.val b.val + (b.val : ℤ) * Nat.gcdB a.val b.val) * Nat.gcdA g N
      + (N : ℤ) * Nat.gcdB g N = 1 := by
    rw [← hg2, ← h1, hg1]
  have := congrArg (fun z : ℤ => (z : ZMod N)) key
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero,
    Int.cast_one, ZMod.natCast_zmod_val] at this
  rw [← this]; push_cast; ring

theorem exists_compl_of_addOrderOf_eq {N : ℕ} [NeZero N] (v : ZMod N × ZMod N) (hv : addOrderOf v = N) :
    ∃ w : ZMod N × ZMod N, Function.Bijective (fun p : ZMod N × ZMod N => p.1 • v + p.2 • w) := by
  obtain ⟨a, b⟩ := v
  obtain ⟨x, y, hxy⟩ := exists_bezout_of_addOrderOf_eq a b hv
  refine ⟨(-y, x), Function.bijective_iff_has_inverse.mpr ⟨fun q => (x * q.1 + y * q.2, -b * q.1 + a * q.2), ?_, ?_⟩⟩
  · intro p
    simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk]
    refine Prod.ext ?_ ?_
    · show x * (p.1 * a + p.2 * -y) + y * (p.1 * b + p.2 * x) = p.1
      linear_combination (p.1) * hxy
    · show -b * (p.1 * a + p.2 * -y) + a * (p.1 * b + p.2 * x) = p.2
      linear_combination (p.2) * hxy
  · intro q
    simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk]
    refine Prod.ext ?_ ?_
    · show (x * q.1 + y * q.2) * a + (-b * q.1 + a * q.2) * -y = q.1
      linear_combination (q.1) * hxy
    · show (x * q.1 + y * q.2) * b + (-b * q.1 + a * q.2) * x = q.2
      linear_combination (q.2) * hxy

open WeierstrassCurve WeierstrassCurve.Affine in

theorem exists_generator_image_torsion
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic] (Q : W.toAffine.Point) (hQ : addOrderOf Q = N)
    {V : Type*} [AddCommGroup V] (φ : W.toAffine.Point →+ V) (hφker : φ.ker = AddSubgroup.zmultiples Q) :
    ∃ Q' : V, addOrderOf Q' = N ∧
      (∀ P : W.toAffine.Point, N • P = 0 → φ P ∈ AddSubgroup.zmultiples Q') ∧
      (∀ T ∈ AddSubgroup.zmultiples Q', ∃ P : W.toAffine.Point, N • P = 0 ∧ φ P = T) := by
  classical
  obtain ⟨eT⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (F := K) (K := K) W hN
  have hb : (W⁄K) = W.toAffine := by
    show (W.baseChange K).toAffine = W.toAffine
    rw [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
  rw [hb] at eT

  have hmem : ∀ P : W.toAffine.Point, P ∈ Submodule.torsionBy ℤ W.toAffine.Point N ↔ N • P = 0 := by
    intro P; rw [Submodule.mem_torsionBy_iff]; show ((N : ℤ) • P = 0) ↔ N • P = 0; rw [natCast_zsmul]
  have hQN : N • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  set v : ZMod N × ZMod N := eT.symm ⟨Q, (hmem Q).mpr hQN⟩ with hv_def
  have hv : addOrderOf v = N := by
    rw [hv_def, AddEquiv.addOrderOf_eq]
    have := addOrderOf_injective (Submodule.torsionBy ℤ W.toAffine.Point N).subtype.toAddMonoidHom
      Subtype.val_injective ⟨Q, (hmem Q).mpr hQN⟩

    exact this.symm.trans hQ
  obtain ⟨w, hbij⟩ := exists_compl_of_addOrderOf_eq v hv

  have hsm : ∀ (c : ZMod N) (z : ZMod N × ZMod N), eT (c • z) = c.val • eT z := by
    intro c z
    rw [← map_nsmul]; congr 1
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    ext <;> simp [nsmul_eq_mul]

  have hzmod : ∀ (z : ℤ) (P : W.toAffine.Point), N • P = 0 → z • P = ((z : ZMod N).val) • P := by
    intro z P hP
    have h1 : (((z : ZMod N).val : ℕ) : ℤ) = z % N := ZMod.val_intCast z
    conv_lhs => rw [← Int.emod_add_mul_ediv z N, add_zsmul, mul_comm, mul_zsmul, natCast_zsmul, hP,
      zsmul_zero, add_zero, ← h1, natCast_zsmul]
  have hQker : φ Q = 0 := by rw [← AddMonoidHom.mem_ker, hφker]; exact AddSubgroup.mem_zmultiples Q

  set R : W.toAffine.Point := (eT w).1 with hR
  have hRN : N • R = 0 := (hmem R).mp (eT w).2
  have hRsub : ∀ m : ℕ, ((m • eT w : Submodule.torsionBy ℤ W.toAffine.Point N) : W.toAffine.Point) = m • R := by
    intro m; rw [hR]; rfl
  have hQsub : ∀ m : ℕ, ((m • eT v : Submodule.torsionBy ℤ W.toAffine.Point N) : W.toAffine.Point) = m • Q := by
    intro m; rw [hv_def, AddEquiv.apply_symm_apply]; rfl
  refine ⟨φ R, ?_, ?_, ?_⟩
  ·
    apply Nat.dvd_antisymm
    · exact addOrderOf_dvd_of_nsmul_eq_zero (by rw [← map_nsmul, hRN, map_zero])
    · have key : ∀ m : ℕ, m • φ R = 0 → N ∣ m := by
        intro m hm
        rw [← map_nsmul, ← AddMonoidHom.mem_ker, hφker, AddSubgroup.mem_zmultiples_iff] at hm
        obtain ⟨z, hz⟩ := hm
        rw [hzmod z Q hQN] at hz

        set c : ZMod N := (z : ZMod N)
        have h2 : eT (c • v) = eT ((m : ZMod N) • w) := by
          apply Subtype.ext
          rw [hsm, hsm, hQsub, hRsub, hz, ZMod.val_natCast]

          exact nsmul_eq_mod_nsmul m hRN
        have h3 : c • v = (m : ZMod N) • w := eT.injective h2
        have h4 : (fun p : ZMod N × ZMod N => p.1 • v + p.2 • w) (c, -(m : ZMod N))
            = (fun p : ZMod N × ZMod N => p.1 • v + p.2 • w) (0, 0) := by
          simp only [zero_smul, add_zero, neg_smul, h3]; exact add_neg_cancel _
        have h5 := hbij.1 h4
        simp only [Prod.mk.injEq, neg_eq_zero] at h5
        exact (ZMod.natCast_eq_zero_iff m N).mp h5.2
      exact key _ (addOrderOf_nsmul_eq_zero _)
  ·
    intro P hP
    obtain ⟨p, hp⟩ := hbij.2 (eT.symm ⟨P, (hmem P).mpr hP⟩)
    have h1 := congrArg (fun z => ((eT z : Submodule.torsionBy ℤ W.toAffine.Point N) : W.toAffine.Point)) hp
    simp only [map_add, AddEquiv.apply_symm_apply, Submodule.coe_add] at h1
    rw [hsm, hsm, hQsub, hRsub] at h1

    rw [← h1, map_add, map_nsmul, map_nsmul, hQker, nsmul_zero, zero_add]
    exact (AddSubgroup.zmultiples (φ R)).nsmul_mem (AddSubgroup.mem_zmultiples _) _
  ·
    intro T hT
    obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hT
    refine ⟨z • R, ?_, by rw [map_zsmul]⟩
    rw [smul_comm, hRN, zsmul_zero]

section Subst

variable (C C' : VariableChange K)

theorem vcInvEmbedding_mul (P : K × K) :
    vcInvEmbedding (C * C') P = vcInvEmbedding C (vcInvEmbedding C' P) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have hu' : (C'.u : K) ≠ 0 := C'.u.ne_zero
  simp only [vcInvEmbedding_apply, vcXInv, vcYInv, VariableChange.mul_def, Units.val_mul,
    Units.val_inv_eq_inv_val, mul_inv, Prod.mk.injEq]
  constructor
  · field_simp; ring
  · field_simp; ring

theorem vcInvEmbedding_inv (P : K × K) :
    vcInvEmbedding C⁻¹ P = (vcX C P.1, vcY C P.1 P.2) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [vcInvEmbedding_apply, vcXInv, vcYInv, vcX, vcY, VariableChange.inv_def, inv_inv,
    Units.val_inv_eq_inv_val, Prod.mk.injEq]
  constructor
  · field_simp; ring
  · field_simp; ring

theorem vcFun_coordsOrZero (W : WeierstrassCurve K) (P : (C • W).toAffine.Point) (hP : P ≠ 0) :
    (Point.vcFun C W.toAffine P).coordsOrZero = (vcX C P.coordsOrZero.1, vcY C P.coordsOrZero.1 P.coordsOrZero.2) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · rfl

theorem vcFun_ne_zero (W : WeierstrassCurve K) (P : (C • W).toAffine.Point) (hP : P ≠ 0) :
    Point.vcFun C W.toAffine P ≠ 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · exact fun h' => by cases h'

theorem vcFun_vcInvFun (W : WeierstrassCurve K) (P : W.toAffine.Point) :
    Point.vcFun C W.toAffine (Point.vcInvFun C W.toAffine P) = P :=
  Point.vcFun_rightInverse (C := C) (W := W.toAffine) P

theorem vcInvFun_vcFun (W : WeierstrassCurve K) (P : (C • W).toAffine.Point) :
    Point.vcInvFun C W.toAffine (Point.vcFun C W.toAffine P) = P :=
  Point.vcFun_leftInverse (C := C) (W := W.toAffine) P

end Subst

section Conj

theorem castPt_zero {V V' : WeierstrassCurve K} (h : V = V') : castPt h (0 : V.toAffine.Point) = 0 := map_zero _

theorem castPt_ne_zero {V V' : WeierstrassCurve K} (h : V = V') {P : V.toAffine.Point} (hP : P ≠ 0) : castPt h P ≠ 0 :=
  fun h0 => hP ((castPt h).injective (h0.trans (castPt_zero h).symm))

theorem conj_mem_stab (C : VariableChange K) (W W'' : WeierstrassCurve K) (hC : C • W = W'')
    (Q : W.toAffine.Point) (H'' : Set W''.toAffine.Point)
    (hfwd : ∀ T ∈ AddSubgroup.zmultiples Q, T ≠ 0 → castPt hC (Point.vcInvFun C W.toAffine T) ∈ H'')
    (hbwd : ∀ S ∈ H'', Point.vcFun C W.toAffine (castPt hC.symm S) ∈ AddSubgroup.zmultiples Q)
    (γ'' : VariableChange K) (hγ'' : γ'' • W'' = W'')
    (hst : ∀ S ∈ H'', ∃ S' ∈ H'', HEq (Point.vcInvFun γ'' W''.toAffine S) S') :
    (C⁻¹ * γ'' * C) • W = W ∧
      ∀ T ∈ AddSubgroup.zmultiples Q, ∃ T' ∈ AddSubgroup.zmultiples Q,
        HEq (Point.vcInvFun (C⁻¹ * γ'' * C) W.toAffine T) T' := by
  have hsm : (C⁻¹ * γ'' * C) • W = W := by
    rw [mul_smul, mul_smul, hC, hγ'', ← hC, inv_smul_smul]
  refine ⟨hsm, fun T hT => ?_⟩
  by_cases hT0 : T = 0
  · refine ⟨0, zero_mem _, ?_⟩
    rw [← castPt_eq_iff_heq hsm, hT0]
    exact map_zero _
  · set S := castPt hC (Point.vcInvFun C W.toAffine T) with hS
    have hSmem : S ∈ H'' := hfwd T hT hT0
    have hS0 : S ≠ 0 := castPt_ne_zero hC (vcInvFun_ne_zero C W T hT0)
    obtain ⟨S', hS'mem, hheq⟩ := hst S hSmem
    have hS'0 : S' ≠ 0 := ne_zero_of_heq hγ'' _ _ hheq (vcInvFun_ne_zero γ'' W'' S hS0)
    set T' := Point.vcFun C W.toAffine (castPt hC.symm S') with hT'
    refine ⟨T', hbwd S' hS'mem, ?_⟩
    rw [← castPt_eq_iff_heq hsm]
    have hT'0 : T' ≠ 0 := vcFun_ne_zero C W _ (castPt_ne_zero hC.symm hS'0)
    apply eq_of_coordsOrZero_eq (castPt_ne_zero hsm (vcInvFun_ne_zero _ W T hT0)) hT'0
    rw [coordsOrZero_castPt, ← vcInvEmbedding_coordsOrZero _ W T hT0, vcInvEmbedding_mul, vcInvEmbedding_mul,
      vcInvEmbedding_coordsOrZero C W T hT0, ← coordsOrZero_castPt hC (Point.vcInvFun C W.toAffine T), ← hS,
      vcInvEmbedding_coordsOrZero γ'' W'' S hS0, coordsOrZero_eq_of_heq hγ'' _ _ hheq, vcInvEmbedding_inv,
      hT', vcFun_coordsOrZero C W _ (castPt_ne_zero hC.symm hS'0), coordsOrZero_castPt]

theorem conj_injective (C : VariableChange K) : Function.Injective (fun γ : VariableChange K => C⁻¹ * γ * C) := by
  intro a b h
  simpa using congrArg (fun γ => C * γ * C⁻¹) h

end Conj

section Assembly

theorem castPt_symm_castPt {V V' : WeierstrassCurve K} (h : V = V') (P : V.toAffine.Point) :
    castPt h.symm (castPt h P) = P := by
  subst h; rfl

theorem equivOfVariableChangeEq_eq (C : VariableChange K) (W V : WeierstrassCurve K) (h : C • W = V)
    (S : V.toAffine.Point) :
    Point.equivOfVariableChangeEq (W := W.toAffine) h S = Point.vcFun C W.toAffine (castPt h.symm S) := by
  subst h; rfl

theorem stab_dual
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic]
    (Q : W.toAffine.Point) (hQ : addOrderOf Q = N) (hΔ : (W.fullKernelQuotient Q N).Δ ≠ 0)
    (φ : W.toAffine.Point →+ (W.fullKernelQuotient Q N).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ P : W.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
      (φ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2))) :
    Nat.card {γ : VariableChange K // γ • W = W ∧
        ∀ T ∈ AddSubgroup.zmultiples Q, ∃ T' ∈ AddSubgroup.zmultiples Q,
          HEq (Point.vcInvFun γ W.toAffine T) T'} =
      Nat.card {γ' : VariableChange K // γ' • (W.fullKernelQuotient Q N) = W.fullKernelQuotient Q N ∧
        ∀ P : W.toAffine.Point, N • P = 0 → ∃ P' : W.toAffine.Point, N • P' = 0 ∧
          HEq (Point.vcInvFun γ' (W.fullKernelQuotient Q N).toAffine (φ P)) (φ P')} := by
  classical
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)

  letI instW' : (W.fullKernelQuotient Q N).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩

  let ι₁ : {γ : VariableChange K // γ • W = W ∧
        ∀ T ∈ AddSubgroup.zmultiples Q, ∃ T' ∈ AddSubgroup.zmultiples Q,
          HEq (Point.vcInvFun γ W.toAffine T) T'} →
      {γ' : VariableChange K // γ' • (W.fullKernelQuotient Q N) = W.fullKernelQuotient Q N ∧
        ∀ P : W.toAffine.Point, N • P = 0 → ∃ P' : W.toAffine.Point, N • P' = 0 ∧
          HEq (Point.vcInvFun γ' (W.fullKernelQuotient Q N).toAffine (φ P)) (φ P')} :=
    fun γ => ⟨γ.1, mem_stab_quotient γ.1 W γ.2.1 Q N hQ hNpos γ.2.2 φ hφker hφ⟩
  have hι₁ : Function.Injective ι₁ := fun a b h => by
    have h' : (ι₁ a).1 = (ι₁ b).1 := congrArg Subtype.val h
    exact Subtype.ext h'

  obtain ⟨Q', hQ'ord, hQ'sub, hQ'sur⟩ := exists_generator_image_torsion hN W Q hQ φ hφker

  obtain ⟨φ', hφ'ker, hφ'⟩ := WeierstrassCurve.exists_fullKernelHom (W.fullKernelQuotient Q N) hN Q' hQ'ord
  have hΔ' : ((W.fullKernelQuotient Q N).fullKernelQuotient Q' N).Δ ≠ 0 :=
    WeierstrassCurve.fullKernelQuotient_discriminant_ne_zero N (W.fullKernelQuotient Q N) hN Q' hQ'ord
  obtain ⟨C, hC, hbid⟩ :=
    WeierstrassCurve.exists_variableChange_eq_fullKernelQuotient_fullKernelQuotient_comp_eq_smul
      hN W Q hQ hΔ φ hφker hφ Q' hQ'ord hQ'sub hΔ' φ' hφ'ker hφ'
  have hsurj : Function.Surjective φ :=
    WeierstrassCurve.fullKernelHom_surjective_of_isAlgClosed W hN Q hQ φ hφker hφ
  have hsurj' : Function.Surjective φ' :=
    WeierstrassCurve.fullKernelHom_surjective_of_isAlgClosed (W.fullKernelQuotient Q N) hN Q' hQ'ord φ' hφ'ker hφ'

  let H'' : Set ((W.fullKernelQuotient Q N).fullKernelQuotient Q' N).toAffine.Point :=
    {S | ∃ P', N • P' = 0 ∧ φ' P' = S}
  have hfwd : ∀ T ∈ AddSubgroup.zmultiples Q, T ≠ 0 → castPt hC (Point.vcInvFun C W.toAffine T) ∈ H'' := by
    intro T hT _
    obtain ⟨P₀, hP₀⟩ := (hsurj'.comp hsurj) (castPt hC (Point.vcInvFun C W.toAffine T))
    simp only [Function.comp_apply] at hP₀
    have hNP₀ : N • P₀ = T := by
      have h1 := hbid P₀
      rw [hP₀, equivOfVariableChangeEq_eq, castPt_symm_castPt, vcFun_vcInvFun, natCast_zsmul] at h1
      exact h1.symm
    refine ⟨φ P₀, ?_, hP₀⟩
    rw [← map_nsmul, hNP₀, ← AddMonoidHom.mem_ker, hφker]; exact hT
  have hbwd : ∀ S ∈ H'', Point.vcFun C W.toAffine (castPt hC.symm S) ∈ AddSubgroup.zmultiples Q := by
    rintro S ⟨P', hP', rfl⟩
    obtain ⟨P, rfl⟩ := hsurj P'
    rw [← equivOfVariableChangeEq_eq C W _ hC, hbid P, natCast_zsmul, ← hφker, AddMonoidHom.mem_ker, map_nsmul]
    exact hP'

  have hB : ∀ γ' : {γ' : VariableChange K // γ' • (W.fullKernelQuotient Q N) = W.fullKernelQuotient Q N ∧
        ∀ P : W.toAffine.Point, N • P = 0 → ∃ P' : W.toAffine.Point, N • P' = 0 ∧
          HEq (Point.vcInvFun γ' (W.fullKernelQuotient Q N).toAffine (φ P)) (φ P')},
      (C⁻¹ * γ'.1 * C) • W = W ∧
        ∀ T ∈ AddSubgroup.zmultiples Q, ∃ T' ∈ AddSubgroup.zmultiples Q,
          HEq (Point.vcInvFun (C⁻¹ * γ'.1 * C) W.toAffine T) T' := by
    rintro ⟨γ', hγ'W', hγ'st⟩

    have hst' : ∀ T ∈ AddSubgroup.zmultiples Q', ∃ T' ∈ AddSubgroup.zmultiples Q',
        HEq (Point.vcInvFun γ' (W.fullKernelQuotient Q N).toAffine T) T' := by
      intro T hT
      obtain ⟨P, hP, rfl⟩ := hQ'sur T hT
      obtain ⟨P'', hP'', hheq⟩ := hγ'st P hP
      exact ⟨φ P'', hQ'sub P'' hP'', hheq⟩
    obtain ⟨hγ'W'', hγ'st''⟩ :=
      mem_stab_quotient γ' (W.fullKernelQuotient Q N) hγ'W' Q' N hQ'ord hNpos hst' φ' hφ'ker hφ'
    have hst'' : ∀ S ∈ H'', ∃ S' ∈ H'',
        HEq (Point.vcInvFun γ' ((W.fullKernelQuotient Q N).fullKernelQuotient Q' N).toAffine S) S' := by
      rintro S ⟨P', hP', rfl⟩
      obtain ⟨P''', hP''', hheq⟩ := hγ'st'' P' hP'
      exact ⟨φ' P''', ⟨P''', hP''', rfl⟩, hheq⟩
    exact conj_mem_stab C W _ hC Q H'' hfwd hbwd γ' hγ'W'' hst''
  let ι₂ : {γ' : VariableChange K // γ' • (W.fullKernelQuotient Q N) = W.fullKernelQuotient Q N ∧
        ∀ P : W.toAffine.Point, N • P = 0 → ∃ P' : W.toAffine.Point, N • P' = 0 ∧
          HEq (Point.vcInvFun γ' (W.fullKernelQuotient Q N).toAffine (φ P)) (φ P')} →
      {γ : VariableChange K // γ • W = W ∧
        ∀ T ∈ AddSubgroup.zmultiples Q, ∃ T' ∈ AddSubgroup.zmultiples Q,
          HEq (Point.vcInvFun γ W.toAffine T) T'} :=
    fun γ' => ⟨C⁻¹ * γ'.1 * C, hB γ'⟩
  have hι₂ : Function.Injective ι₂ := fun a b h =>
    Subtype.ext (conj_injective C (congrArg Subtype.val h))

  obtain ⟨f, hf⟩ := Function.Embedding.schroeder_bernstein hι₁ hι₂
  exact Nat.card_congr (Equiv.ofBijective f hf)

end Assembly

end StabDual
p2m_reactivate "P2MW.S_WeierstrassCurve_natCard_variableChange_stabilizer_eq_of_fullKernelQuotient.StabDual"

open WeierstrassCurve WeierstrassCurve.Affine in
theorem solution
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic]
    (Q : W.toAffine.Point) (hQ : addOrderOf Q = N) (hΔ : (W.fullKernelQuotient Q N).Δ ≠ 0)
    (φ : W.toAffine.Point →+ (W.fullKernelQuotient Q N).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ P : W.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
      (φ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)))
    :
    Nat.card {γ : VariableChange K // γ • W = W ∧
        ∀ T ∈ AddSubgroup.zmultiples Q, ∃ T' ∈ AddSubgroup.zmultiples Q,
          HEq (Point.vcInvFun γ W.toAffine T) T'} =
      Nat.card {γ' : VariableChange K // γ' • (W.fullKernelQuotient Q N) = W.fullKernelQuotient Q N ∧
        ∀ P : W.toAffine.Point, N • P = 0 → ∃ P' : W.toAffine.Point, N • P' = 0 ∧
          HEq (Point.vcInvFun γ' (W.fullKernelQuotient Q N).toAffine (φ P)) (φ P')} :=
  StabDual.stab_dual hN W Q hQ hΔ φ hφker hφ

end S_WeierstrassCurve_natCard_variableChange_stabilizer_eq_of_fullKernelQuotient
end P2MW
export P2MW.S_WeierstrassCurve_natCard_variableChange_stabilizer_eq_of_fullKernelQuotient (solution)
