-- Prove2me | solution 1 for WeierstrassCurve.exists_quotientDatum_of_galois_stable_primeCard
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/6c2b069d-3207-5b2f-b647-d9b70206c20f

import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_VeluEquivariance
import Theorems.Thm_WeierstrassCurve_exists_integral_veluQuotient_rescale_of_galois_stable
import Theorems.Thm_WeierstrassCurve_dvd_discriminant_not_dvd_c4_integral_veluQuotient_rescale
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_veluCoord_iff_of_multiplicative
import Theorems.Thm_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_algebraicClosure
import Theorems.Thm_ValuationSubring_valuation_natCast_eq_one_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_quotientDatum_of_galois_stable_primeCard
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.IsCurveOver.instNontrivialKaehler"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"

p2m_open "WeierstrassCurve~card WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring"

private lemma vcX_injective' {K : Type*} [Field K] {C : VariableChange K} :
    Function.Injective (vcX C) := by
  intro a b h
  have h' := congrArg (vcXInv C) h
  simpa using h'

private lemma vcY_injective' {K : Type*} [Field K] {C : VariableChange K} (x' : K) :
    Function.Injective (vcY C x') := by
  intro a b h
  have h' := congrArg (vcYInv C (vcX C x')) h
  simpa using h'

private lemma negY_vc {K : Type*} [Field K] {C : VariableChange K}
    {W : WeierstrassCurve.Affine K} (x' y' : K) :
    W.negY (vcX C x') (vcY C x' y') = vcY C x' ((C • W).toAffine.negY x' y') := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [Affine.negY, vcX, vcY, variableChange_a₁, variableChange_a₃,
    Units.val_inv_eq_inv_val]
  field_simp
  ring

private lemma Yeq_vc_iff {K : Type*} [Field K] {C : VariableChange K}
    {W : WeierstrassCurve.Affine K} (x₁' x₂' y₁' y₂' : K) :
    (vcX C x₁' = vcX C x₂' ∧ vcY C x₁' y₁' = W.negY (vcX C x₂') (vcY C x₂' y₂'))
      ↔ (x₁' = x₂' ∧ y₁' = (C • W).toAffine.negY x₂' y₂') := by
  constructor
  · rintro ⟨hx, hy⟩
    have hx' : x₁' = x₂' := vcX_injective' hx
    subst hx'
    refine ⟨rfl, ?_⟩
    rw [negY_vc x₁' y₂'] at hy
    exact vcY_injective' x₁' hy
  · rintro ⟨hx, hy⟩
    subst hx
    exact ⟨rfl, by rw [negY_vc x₁' y₂', hy]⟩

private lemma partialX_aux' {K : Type*} [Field K] {C : VariableChange K}
    {W : WeierstrassCurve.Affine K} (x' y' : K) :
    W.a₁ * vcY C x' y' - (3 * vcX C x' ^ 2 + 2 * W.a₂ * vcX C x' + W.a₄)
      + C.s * (2 * vcY C x' y' + W.a₁ * vcX C x' + W.a₃)
    = (C.u : K) ^ 4 *
      ((C • W).a₁ * y' - (3 * x' ^ 2 + 2 * (C • W).a₂ * x' + (C • W).a₄)) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [vcX, vcY, variableChange_a₁, variableChange_a₂, variableChange_a₄,
    Units.val_inv_eq_inv_val]
  field_simp
  ring

private lemma partialY_aux' {K : Type*} [Field K] {C : VariableChange K}
    {W : WeierstrassCurve.Affine K} (x' y' : K) :
    2 * vcY C x' y' + W.a₁ * vcX C x' + W.a₃
      = (C.u : K) ^ 3 * (2 * y' + (C • W).a₁ * x' + (C • W).a₃) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [vcX, vcY, variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp
  ring

private lemma slope_vc {K : Type*} [Field K] [DecidableEq K] {C : VariableChange K}
    {W : WeierstrassCurve.Affine K} (x₁' x₂' y₁' y₂' : K)
    (h₁ : (C • W).toAffine.Equation x₁' y₁') (h₂ : (C • W).toAffine.Equation x₂' y₂')
    (hxy : ¬(x₁' = x₂' ∧ y₁' = (C • W).toAffine.negY x₂' y₂')) :
    W.slope (vcX C x₁') (vcX C x₂') (vcY C x₁' y₁') (vcY C x₂' y₂')
      = (C.u : K) * (C • W).toAffine.slope x₁' x₂' y₁' y₂' + C.s := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  by_cases hx : x₁' = x₂'
  · have hy : y₁' ≠ (C • W).toAffine.negY x₂' y₂' := fun h => hxy ⟨hx, h⟩
    have hyy : y₁' = y₂' := (Affine.Y_eq_of_X_eq h₁ h₂ hx).resolve_right hy
    subst hx
    subst hyy
    have hyW : vcY C x₁' y₁' ≠ W.negY (vcX C x₁') (vcY C x₁' y₁') := by
      intro h
      exact hy ((Yeq_vc_iff x₁' x₁' y₁' y₁').mp ⟨rfl, h⟩).2
    rw [Affine.slope_of_Y_ne rfl hyW, Affine.slope_of_Y_ne rfl hy]
    have hd : vcY C x₁' y₁' - W.negY (vcX C x₁') (vcY C x₁' y₁')
        = (C.u : K) ^ 3 * (y₁' - (C • W).toAffine.negY x₁' y₁') := by
      rw [negY_vc x₁' y₁']
      simp only [vcY]
      ring
    have hPYden : y₁' - (C • W).toAffine.negY x₁' y₁'
        = 2 * y₁' + (C • W).a₁ * x₁' + (C • W).a₃ := by
      simp only [Affine.negY]
      ring
    have hn : 3 * vcX C x₁' ^ 2 + 2 * W.a₂ * vcX C x₁' + W.a₄ - W.a₁ * vcY C x₁' y₁'
        = (C.u : K) ^ 4 * (3 * x₁' ^ 2 + 2 * (C • W).a₂ * x₁'
            + (C • W).a₄ - (C • W).a₁ * y₁')
          + C.s * ((C.u : K) ^ 3 * (y₁' - (C • W).toAffine.negY x₁' y₁')) := by
      have hX := partialX_aux' (C := C) (W := W) x₁' y₁'
      have hY := partialY_aux' (C := C) (W := W) x₁' y₁'
      rw [hPYden]
      linear_combination (-1 : K) * hX + C.s * hY
    rw [hd, hn]
    have hden' : y₁' - (C • W).toAffine.negY x₁' y₁' ≠ 0 := sub_ne_zero_of_ne hy
    field_simp
  · have hxW : vcX C x₁' ≠ vcX C x₂' := fun h => hx (vcX_injective' h)
    rw [Affine.slope_of_X_ne hxW, Affine.slope_of_X_ne hx]
    have hd : vcX C x₁' - vcX C x₂' = (C.u : K) ^ 2 * (x₁' - x₂') := by
      simp only [vcX]; ring
    have hn : vcY C x₁' y₁' - vcY C x₂' y₂'
        = (C.u : K) ^ 3 * (y₁' - y₂') + (C.u : K) ^ 2 * C.s * (x₁' - x₂') := by
      simp only [vcY]; ring
    rw [hd, hn]
    have hxne : x₁' - x₂' ≠ 0 := sub_ne_zero_of_ne hx
    field_simp

private lemma addX_vc {K : Type*} [Field K] {C : VariableChange K}
    {W : WeierstrassCurve.Affine K} (x₁' x₂' ℓ : K) :
    W.addX (vcX C x₁') (vcX C x₂') ((C.u : K) * ℓ + C.s)
      = vcX C ((C • W).toAffine.addX x₁' x₂' ℓ) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [Affine.addX, vcX, variableChange_a₁, variableChange_a₂,
    Units.val_inv_eq_inv_val]
  field_simp
  ring

private lemma addY_vc {K : Type*} [Field K] {C : VariableChange K}
    {W : WeierstrassCurve.Affine K} (x₁' x₂' y₁' ℓ : K) :
    W.addY (vcX C x₁') (vcX C x₂') (vcY C x₁' y₁') ((C.u : K) * ℓ + C.s)
      = vcY C ((C • W).toAffine.addX x₁' x₂' ℓ) ((C • W).toAffine.addY x₁' x₂' y₁' ℓ) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY, vcX, vcY,
    variableChange_a₁, variableChange_a₂, variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp
  ring

private lemma some_eq_some' {K : Type*} [Field K] {V : WeierstrassCurve.Affine K}
    {x₁ y₁ x₂ y₂ : K} {h₁ : V.Nonsingular x₁ y₁} {h₂ : V.Nonsingular x₂ y₂}
    (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Point.some x₁ y₁ h₁ : V.Point) = Point.some x₂ y₂ h₂ := by
  subst hx
  subst hy
  rfl

private lemma vcFun_some' {K : Type*} [Field K] [DecidableEq K] {C : VariableChange K}
    {W : WeierstrassCurve.Affine K} {x' y' : K} (h : (C • W).toAffine.Nonsingular x' y') :
    Point.vcFun C W (.some x' y' h)
      = .some (vcX C x') (vcY C x' y') ((nonsingular_variableChange_iff x' y').mp h) := rfl

private lemma vcInvFun_some' {K : Type*} [Field K] [DecidableEq K] {C : VariableChange K}
    {W : WeierstrassCurve.Affine K} {x y : K} (h : W.Nonsingular x y) :
    Point.vcInvFun C W (.some x y h)
      = .some (vcXInv C x) (vcYInv C x y)
        ((nonsingular_variableChange_iff (vcXInv C x) (vcYInv C x y)).mpr
          (by rwa [vcX_vcXInv, vcY_vcYInv])) := rfl

private lemma vcFun_add' {K : Type*} [Field K] [DecidableEq K] {C : VariableChange K}
    {W : WeierstrassCurve.Affine K} (P Q : (C • W).toAffine.Point) :
    Point.vcFun C W (P + Q) = Point.vcFun C W P + Point.vcFun C W Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rfl
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2, Point.vcFun_zero, vcFun_some', vcFun_some']
    have hxyW := (Yeq_vc_iff (W := W) x₁ x₂ y₁ y₂).mpr hxy
    exact (Affine.Point.add_of_Y_eq hxyW.1 hxyW.2).symm
  · have hxyW : ¬(vcX C x₁ = vcX C x₂ ∧ vcY C x₁ y₁ = W.negY (vcX C x₂) (vcY C x₂ y₂)) :=
      fun h => hxy ((Yeq_vc_iff x₁ x₂ y₁ y₂).mp h)
    have hslope := slope_vc (W := W) x₁ x₂ y₁ y₂ h₁.1 h₂.1 hxy
    rw [Affine.Point.add_some hxy, vcFun_some', vcFun_some', vcFun_some',
      Affine.Point.add_some hxyW]
    refine some_eq_some' ?_ ?_
    · rw [hslope, addX_vc]
    · rw [hslope, addY_vc]

private noncomputable def vcHom {K : Type*} [Field K] [DecidableEq K] (C : VariableChange K)
    (W : WeierstrassCurve.Affine K) : (C • W).toAffine.Point →+ W.Point where
  toFun := Point.vcFun C W
  map_zero' := rfl
  map_add' := vcFun_add'

private lemma vcHom_bijective {K : Type*} [Field K] [DecidableEq K] {C : VariableChange K}
    {W : WeierstrassCurve.Affine K} : Function.Bijective (vcHom C W) :=
  ⟨Point.vcFun_leftInverse.injective, Point.vcFun_rightInverse.surjective⟩

private noncomputable def vcAddEquivOfEq {K : Type*} [Field K] [DecidableEq K]
    (C : VariableChange K) {V W' : WeierstrassCurve.Affine K} (h : C • V = W') :
    W'.Point ≃+ V.Point := by
  subst h
  exact AddEquiv.ofBijective (vcHom C V) vcHom_bijective

private lemma vcAddEquivOfEq_symm_some_eq {K : Type*} [Field K] [DecidableEq K]
    {C : VariableChange K} {V W' : WeierstrassCurve.Affine K} (h : C • V = W')
    {x y : K} (hn : V.Nonsingular x y) :
    ∃ hn' : W'.Nonsingular (vcXInv C x) (vcYInv C x y),
      (vcAddEquivOfEq C h).symm (.some x y hn)
        = .some (vcXInv C x) (vcYInv C x y) hn' := by
  subst h
  refine ⟨(nonsingular_variableChange_iff (vcXInv C x) (vcYInv C x y)).mpr
    (by rwa [vcX_vcXInv, vcY_vcYInv]), ?_⟩
  rw [show vcAddEquivOfEq C rfl = AddEquiv.ofBijective (vcHom C V) vcHom_bijective from rfl]
  rw [AddEquiv.symm_apply_eq]
  exact (some_eq_some' (vcX_vcXInv x) (vcY_vcYInv x y)).symm

private lemma some_eq_some2 {K : Type*} [Field K] {V : WeierstrassCurve.Affine K}
    {x₁ y₁ x₂ y₂ : K} {h₁ : V.Nonsingular x₁ y₁} {h₂ : V.Nonsingular x₂ y₂}
    (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Point.some x₁ y₁ h₁ : V.Point) = Point.some x₂ y₂ h₂ := by
  subst hx
  subst hy
  rfl

private lemma nsmul_ne_zero_of_bounds {A : Type*} [AddGroup A] {R : A} {p : ℕ}
    (hR : addOrderOf R = p) {j : ℕ} (hj1 : 1 ≤ j) (hjp : j < p) : j • R ≠ 0 := by
  intro h0
  have hdvd : addOrderOf R ∣ j := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0
  rw [hR] at hdvd
  exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)

private lemma zsmul_emod {A : Type*} [AddGroup A] {R : A} {p : ℕ}
    (hR : addOrderOf R = p) (a : ℤ) : (a % (p : ℤ)) • R = a • R := by
  have hp0 : (p : ℤ) • R = 0 := by
    rw [natCast_zsmul, ← hR]
    exact addOrderOf_nsmul_eq_zero R
  conv_rhs => rw [← Int.emod_add_mul_ediv a (p : ℤ), mul_comm (p : ℤ) (a / (p : ℤ))]
  rw [add_zsmul, mul_zsmul, hp0, smul_zero, add_zero]

private lemma nsmul_emod {A : Type*} [AddGroup A] {R : A} {p : ℕ}
    (hR : addOrderOf R = p) (a : ℕ) : (a % p) • R = a • R := by
  have h : (((a % p : ℕ)) : ℤ) • R = ((a : ℕ) : ℤ) • R := by
    rw [Int.natCast_mod]
    exact zsmul_emod hR (a : ℤ)
  rw [natCast_zsmul, natCast_zsmul] at h
  exact h

private lemma nsmul_cancel {A : Type*} [AddGroup A] {R : A} {p n : ℕ}
    (hR : addOrderOf R = p) (hpn : p = 2 * n + 1) {j₁ j₂ : ℕ}
    (hb₁ : j₁ ≤ n) (hb₂ : j₂ ≤ n) (h : j₁ • R = j₂ • R) : j₁ = j₂ := by
  rcases le_total j₁ j₂ with hle | hle
  · have hsub : (j₂ - j₁) • R = 0 := by
      rw [sub_nsmul R hle, h]
      exact add_neg_cancel _
    have hdvd : addOrderOf R ∣ j₂ - j₁ := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hsub
    rw [hR] at hdvd
    rcases Nat.eq_zero_or_pos (j₂ - j₁) with h0 | hpos
    · omega
    · exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)
  · have hsub : (j₁ - j₂) • R = 0 := by
      rw [sub_nsmul R hle, h]
      exact add_neg_cancel _
    have hdvd : addOrderOf R ∣ j₁ - j₂ := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hsub
    rw [hR] at hdvd
    rcases Nat.eq_zero_or_pos (j₁ - j₂) with h0 | hpos
    · omega
    · exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)

private lemma nsmul_coords_injOn {F : Type*} [Field F] [DecidableEq F]
    {W : WeierstrassCurve.Affine F}
    {R : W.Point} {p n : ℕ} (hR : addOrderOf R = p) (hpn : p = 2 * n + 1)
    {j₁ j₂ : ℕ} (h₁ : j₁ ∈ Finset.Icc 1 n) (h₂ : j₂ ∈ Finset.Icc 1 n)
    (hEq : (j₁ • R).coordsOrZero = (j₂ • R).coordsOrZero) : j₁ = j₂ := by
  rw [Finset.mem_Icc] at h₁ h₂
  have hne₁ : j₁ • R ≠ 0 := nsmul_ne_zero_of_bounds hR h₁.1 (by omega)
  have hne₂ : j₂ • R ≠ 0 := nsmul_ne_zero_of_bounds hR h₂.1 (by omega)
  have hPts : j₁ • R = j₂ • R := by
    rcases hc₁ : j₁ • R with _ | ⟨x₁, y₁, hn₁⟩
    · exact absurd hc₁ hne₁
    rcases hc₂ : j₂ • R with _ | ⟨x₂, y₂, hn₂⟩
    · exact absurd hc₂ hne₂
    rw [hc₁, hc₂] at hEq
    simp only [Point.coordsOrZero_some, Prod.mk.injEq] at hEq
    exact some_eq_some2 hEq.1 hEq.2
  exact nsmul_cancel hR hpn h₁.2 h₂.2 hPts

set_option maxHeartbeats 3200000 in
private lemma sum_summingSet_index {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) {R : W.toAffine.Point} {p n : ℕ}
    (hR : addOrderOf R = p) (hpn : p = 2 * n + 1) (g : F × F → F) :
    ∑ P ∈ W.oddOrderSummingSet R n, g P
      = ∑ j ∈ Finset.Icc 1 n, g ((j • R).coordsOrZero) := by
  unfold oddOrderSummingSet
  exact Finset.sum_image fun j₁ h₁ j₂ h₂ hEq => nsmul_coords_injOn hR hpn h₁ h₂ hEq

set_option maxHeartbeats 6400000 in
private lemma sum_summingSet_reindex {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) {p n m₀ : ℕ} (hp : p.Prime) (hpn : p = 2 * n + 1)
    {Q : W.toAffine.Point} (hQ : addOrderOf Q = p) (hm₀1 : 1 ≤ m₀) (hm₀p : m₀ < p)
    (g : F × F → F) (hg : ∀ x y : F, g (x, W.toAffine.negY x y) = g (x, y)) :
    ∑ j ∈ Finset.Icc 1 n, g ((j • (m₀ • Q)).coordsOrZero)
      = ∑ j ∈ Finset.Icc 1 n, g ((j • Q).coordsOrZero) := by
  have hpm₀ : ¬ p ∣ m₀ := fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega)
  have hmod : ∀ j, j ∈ Finset.Icc 1 n → 1 ≤ j * m₀ % p ∧ j * m₀ % p < p := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hpj : ¬ p ∣ j := fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega)
    have hpjm : ¬ p ∣ j * m₀ := fun hd => ((Nat.Prime.dvd_mul hp).mp hd).elim hpj hpm₀
    have h1 : j * m₀ % p ≠ 0 := fun h0 => hpjm (Nat.dvd_of_mod_eq_zero h0)
    exact ⟨by omega, Nat.mod_lt _ (by omega)⟩

  have hψval : ∀ j, j ∈ Finset.Icc 1 n →
      g ((j • (m₀ • Q)).coordsOrZero)
        = g (((if j * m₀ % p ≤ n then j * m₀ % p else p - j * m₀ % p) • Q).coordsOrZero) := by
    intro j hj
    have hjr := hmod j hj
    have hsmul : j • (m₀ • Q) = (j * m₀ % p) • Q := by
      rw [← mul_nsmul', nsmul_emod hQ]
    by_cases hrn : j * m₀ % p ≤ n
    · rw [if_pos hrn, hsmul]
    · rw [if_neg hrn, hsmul]

      have hneg : (p - j * m₀ % p) • Q = - ((j * m₀ % p) • Q) := by
        apply eq_neg_of_add_eq_zero_left
        rw [← add_nsmul, Nat.sub_add_cancel (le_of_lt hjr.2), ← hQ]
        exact addOrderOf_nsmul_eq_zero Q
      rcases hcr : (j * m₀ % p) • Q with _ | ⟨xr, yr, hnr⟩
      · exact absurd hcr (nsmul_ne_zero_of_bounds hQ hjr.1 hjr.2)
      rw [hneg, hcr, Point.neg_some]
      simp only [Point.coordsOrZero_some]
      exact (hg xr yr).symm
  rw [Finset.sum_congr rfl hψval]

  have hcop : Nat.gcd p m₀ = 1 := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm₀
  have hψmem : ∀ j, j ∈ Finset.Icc 1 n →
      (if j * m₀ % p ≤ n then j * m₀ % p else p - j * m₀ % p) ∈ Finset.Icc 1 n := by
    intro j hj
    have hjr := hmod j hj
    rw [Finset.mem_Icc]
    by_cases hrn : j * m₀ % p ≤ n
    · rw [if_pos hrn]; omega
    · rw [if_neg hrn]; omega
  have hψinj : ∀ j₁, j₁ ∈ Finset.Icc 1 n → ∀ j₂, j₂ ∈ Finset.Icc 1 n →
      (if j₁ * m₀ % p ≤ n then j₁ * m₀ % p else p - j₁ * m₀ % p)
        = (if j₂ * m₀ % p ≤ n then j₂ * m₀ % p else p - j₂ * m₀ % p) → j₁ = j₂ := by
    intro j₁ hj₁ j₂ hj₂ hψeq
    have hr₁ := hmod j₁ hj₁
    have hr₂ := hmod j₂ hj₂
    rw [Finset.mem_Icc] at hj₁ hj₂
    have hcancel : j₁ * m₀ % p = j₂ * m₀ % p → j₁ = j₂ := by
      intro hmeq
      have hj₁₂ : j₁ ≡ j₂ [MOD p] := Nat.ModEq.cancel_right_of_coprime hcop hmeq
      have e₁ : j₁ % p = j₁ := Nat.mod_eq_of_lt (by omega)
      have e₂ : j₂ % p = j₂ := Nat.mod_eq_of_lt (by omega)
      unfold Nat.ModEq at hj₁₂
      omega
    have hanti : j₁ * m₀ % p + j₂ * m₀ % p = p → False := by
      intro hsum
      have hdvd : p ∣ (j₁ + j₂) * m₀ := by
        apply Nat.dvd_of_mod_eq_zero
        rw [add_mul, Nat.add_mod, hsum, Nat.mod_self]
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
      · exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
      · exact hpm₀ h
    by_cases h₁ : j₁ * m₀ % p ≤ n <;> by_cases h₂ : j₂ * m₀ % p ≤ n
    · rw [if_pos h₁, if_pos h₂] at hψeq
      exact hcancel hψeq
    · rw [if_pos h₁, if_neg h₂] at hψeq
      exact absurd (by omega : j₂ * m₀ % p + j₁ * m₀ % p = p) (fun hs => hanti (by omega))
    · rw [if_neg h₁, if_pos h₂] at hψeq
      exact absurd (by omega : j₁ * m₀ % p + j₂ * m₀ % p = p) hanti
    · rw [if_neg h₁, if_neg h₂] at hψeq
      exact hcancel (by omega)
  have himg : (Finset.Icc 1 n).image
      (fun j => if j * m₀ % p ≤ n then j * m₀ % p else p - j * m₀ % p) = Finset.Icc 1 n := by
    apply Finset.eq_of_subset_of_card_le
    · intro r hr
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
      exact hψmem j hj
    · rw [Finset.card_image_of_injOn
        (fun a ha b hb h => hψinj a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) h)]
  calc ∑ j ∈ Finset.Icc 1 n,
        g (((if j * m₀ % p ≤ n then j * m₀ % p else p - j * m₀ % p) • Q).coordsOrZero)
      = ∑ r ∈ (Finset.Icc 1 n).image
          (fun j => if j * m₀ % p ≤ n then j * m₀ % p else p - j * m₀ % p),
          g ((r • Q).coordsOrZero) :=
        (Finset.sum_image (f := fun r => g ((r • Q).coordsOrZero)) hψinj).symm
    _ = ∑ j ∈ Finset.Icc 1 n, g ((j • Q).coordsOrZero) := by rw [himg]

set_option maxHeartbeats 6400000 in

private lemma sum_summingSet_eq_of_zmultiples {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) {p n : ℕ} (hp : p.Prime) (hpn : p = 2 * n + 1)
    {Q Q' : W.toAffine.Point} (hQ : addOrderOf Q = p) (hQ' : addOrderOf Q' = p)
    (hmem : Q' ∈ AddSubgroup.zmultiples Q) (g : F × F → F)
    (hg : ∀ x y : F, g (x, W.toAffine.negY x y) = g (x, y)) :
    ∑ P ∈ W.oddOrderSummingSet Q' n, g P = ∑ P ∈ W.oddOrderSummingSet Q n, g P := by
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  have hpne : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (by omega)
  have hm₀cast : (((m % (p : ℤ)).toNat : ℤ)) = m % (p : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg m hpne)
  have hm₀Q : (m % (p : ℤ)).toNat • Q = Q' := by
    rw [← natCast_zsmul, hm₀cast, zsmul_emod hQ, hm]
  have hm₀p : (m % (p : ℤ)).toNat < p := by
    have h0 : (0 : ℤ) ≤ m % (p : ℤ) := Int.emod_nonneg m hpne
    have hlt : m % (p : ℤ) < (p : ℤ) := Int.emod_lt_of_pos m (by exact_mod_cast hp.pos)
    omega
  have hm₀1 : 1 ≤ (m % (p : ℤ)).toNat := by
    rcases Nat.eq_zero_or_pos (m % (p : ℤ)).toNat with h0 | h1
    · exfalso
      rw [h0, zero_nsmul] at hm₀Q
      rw [← hm₀Q, AddMonoid.addOrderOf_eq_one_iff.mpr rfl] at hQ'
      have := hp.one_lt
      omega
    · exact h1
  calc ∑ P ∈ W.oddOrderSummingSet Q' n, g P
      = ∑ j ∈ Finset.Icc 1 n, g ((j • Q').coordsOrZero) := sum_summingSet_index W hQ' hpn g
    _ = ∑ j ∈ Finset.Icc 1 n, g ((j • ((m % (p : ℤ)).toNat • Q)).coordsOrZero) := by
        rw [hm₀Q]
    _ = ∑ j ∈ Finset.Icc 1 n, g ((j • Q).coordsOrZero) :=
        sum_summingSet_reindex W hp hpn hQ hm₀1 hm₀p g hg
    _ = ∑ P ∈ W.oddOrderSummingSet Q n, g P := (sum_summingSet_index W hQ hpn g).symm

private lemma veluX_summingSet_congr {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) {p n : ℕ} (hp : p.Prime) (hpn : p = 2 * n + 1)
    {Q Q' : W.toAffine.Point} (hQ : addOrderOf Q = p) (hQ' : addOrderOf Q' = p)
    (hmem : Q' ∈ AddSubgroup.zmultiples Q) (z : F) :
    W.veluX (W.oddOrderSummingSet Q' n) z = W.veluX (W.oddOrderSummingSet Q n) z := by
  unfold veluX
  congr 1
  exact sum_summingSet_eq_of_zmultiples W hp hpn hQ hQ' hmem
    (fun P => W.veluT P.1 P.2 / (z - P.1) + W.veluU P.1 P.2 / (z - P.1) ^ 2)
    (fun x y => by simp only [veluT_negY, veluU_negY])

private lemma veluY_summand_flip {F : Type*} [Field F] (W : WeierstrassCurve F)
    (z w x₀ y₀ : F) :
    W.veluU x₀ (W.toAffine.negY x₀ y₀) * (2 * w + W.a₁ * z + W.a₃) / (z - x₀) ^ 3
      + W.veluT x₀ (W.toAffine.negY x₀ y₀) * (W.a₁ * (z - x₀) + w - W.toAffine.negY x₀ y₀)
          / (z - x₀) ^ 2
      + (W.a₁ * W.veluU x₀ (W.toAffine.negY x₀ y₀)
          - W.veluGx x₀ (W.toAffine.negY x₀ y₀) * W.veluGy x₀ (W.toAffine.negY x₀ y₀))
          / (z - x₀) ^ 2
    = W.veluU x₀ y₀ * (2 * w + W.a₁ * z + W.a₃) / (z - x₀) ^ 3
      + W.veluT x₀ y₀ * (W.a₁ * (z - x₀) + w - y₀) / (z - x₀) ^ 2
      + (W.a₁ * W.veluU x₀ y₀ - W.veluGx x₀ y₀ * W.veluGy x₀ y₀) / (z - x₀) ^ 2 := by
  have h := W.veluY_singleton_negY x₀ y₀ z w
  simp only [veluY, Finset.sum_singleton] at h
  linear_combination -h

private lemma veluY_summingSet_congr {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) {p n : ℕ} (hp : p.Prime) (hpn : p = 2 * n + 1)
    {Q Q' : W.toAffine.Point} (hQ : addOrderOf Q = p) (hQ' : addOrderOf Q' = p)
    (hmem : Q' ∈ AddSubgroup.zmultiples Q) (z w : F) :
    W.veluY (W.oddOrderSummingSet Q' n) z w = W.veluY (W.oddOrderSummingSet Q n) z w := by
  unfold veluY
  congr 1
  exact sum_summingSet_eq_of_zmultiples W hp hpn hQ hQ' hmem
    (fun P => W.veluU P.1 P.2 * (2 * w + W.a₁ * z + W.a₃) / (z - P.1) ^ 3
      + W.veluT P.1 P.2 * (W.a₁ * (z - P.1) + w - P.2) / (z - P.1) ^ 2
      + (W.a₁ * W.veluU P.1 P.2 - W.veluGx P.1 P.2 * W.veluGy P.1 P.2) / (z - P.1) ^ 2)
    (fun x y => veluY_summand_flip W z w x y)

private lemma map_veluX_finset {F F' : Type*} [Field F] [Field F'] [DecidableEq F']
    (W : WeierstrassCurve F) (f : F →+* F') (hf : Function.Injective f)
    (S : Finset (F × F)) (x : F) :
    (W.map f).veluX (S.image (Prod.map ⇑f ⇑f)) (f x) = f (W.veluX S x) := by
  unfold veluX
  rw [map_add, map_sum]
  congr 1
  rw [Finset.sum_image (fun P₁ _ P₂ _ hEq => (hf.prodMap hf) hEq)]
  refine Finset.sum_congr rfl fun P _ => ?_
  simp only [Prod.map_fst, Prod.map_snd, map_veluT, map_veluU, map_div₀, map_sub, map_pow,
    map_add]

private lemma map_veluY_finset {F F' : Type*} [Field F] [Field F'] [DecidableEq F']
    (W : WeierstrassCurve F) (f : F →+* F') (hf : Function.Injective f)
    (S : Finset (F × F)) (x y : F) :
    (W.map f).veluY (S.image (Prod.map ⇑f ⇑f)) (f x) (f y) = f (W.veluY S x y) := by
  unfold veluY
  rw [map_sub, map_sum]
  congr 1
  rw [Finset.sum_image (fun P₁ _ P₂ _ hEq => (hf.prodMap hf) hEq)]
  refine Finset.sum_congr rfl fun P _ => ?_
  simp only [Prod.map_fst, Prod.map_snd, map_veluT, map_veluU, map_veluGx, map_veluGy,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, map_div₀, map_sub, map_pow, map_add,
    map_mul, map_ofNat]

private lemma coordsOrZero_smul (W₀ : WeierstrassCurve ℚ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (P : (WeierstrassCurve.baseChange W₀ (AlgebraicClosure ℚ)).toAffine.Point) :
    (σ • P : (WeierstrassCurve.baseChange W₀ (AlgebraicClosure ℚ)).toAffine.Point).coordsOrZero
      = Prod.map ⇑σ ⇑σ P.coordsOrZero := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [show (Point.zero :
        (WeierstrassCurve.baseChange W₀ (AlgebraicClosure ℚ)).toAffine.Point) = 0 from rfl,
      algEquiv_smul_def, Point.map_zero]
    show ((0, 0) : AlgebraicClosure ℚ × AlgebraicClosure ℚ) = (σ 0, σ 0)
    rw [_root_.map_zero]
  · rw [algEquiv_smul_def, Point.map_some]
    rfl

private lemma image_summingSet_smul (W₀ : WeierstrassCurve ℚ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (R : (WeierstrassCurve.baseChange W₀ (AlgebraicClosure ℚ)).toAffine.Point) (n : ℕ) :
    ((WeierstrassCurve.baseChange W₀ (AlgebraicClosure ℚ)).oddOrderSummingSet R n).image
        (Prod.map ⇑σ ⇑σ)
      = (WeierstrassCurve.baseChange W₀ (AlgebraicClosure ℚ)).oddOrderSummingSet (σ • R) n := by
  unfold oddOrderSummingSet
  rw [Finset.image_image]
  refine Finset.image_congr fun k _ => ?_
  show Prod.map ⇑σ ⇑σ ((k • R).coordsOrZero) = ((k • (σ • R)).coordsOrZero)
  rw [← coordsOrZero_smul]
  congr 1
  exact map_nsmul (DistribSMul.toAddMonoidHom _ σ) k R

private lemma addOrderOf_algEquiv_smul (W₀ : WeierstrassCurve ℚ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (R : (WeierstrassCurve.baseChange W₀ (AlgebraicClosure ℚ)).toAffine.Point) :
    addOrderOf (σ • R) = addOrderOf R :=
  addOrderOf_injective (DistribSMul.toAddMonoidHom _ σ) (MulAction.injective σ) R

private lemma baseChange_fix (W₀ : WeierstrassCurve ℚ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    WeierstrassCurve.map (WeierstrassCurve.baseChange W₀ (AlgebraicClosure ℚ))
        σ.toAlgHom.toRingHom
      = WeierstrassCurve.baseChange W₀ (AlgebraicClosure ℚ) := by
  show WeierstrassCurve.map (WeierstrassCurve.map W₀ (algebraMap ℚ (AlgebraicClosure ℚ)))
      σ.toAlgHom.toRingHom
    = WeierstrassCurve.map W₀ (algebraMap ℚ (AlgebraicClosure ℚ))
  rw [WeierstrassCurve.map_map]
  congr 1
  ext r
  exact σ.toAlgHom.commutes r

private lemma algEquiv_veluX {Wc : WeierstrassCurve (AlgebraicClosure ℚ)}
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hfix : WeierstrassCurve.map Wc σ.toAlgHom.toRingHom = Wc)
    (S : Finset (AlgebraicClosure ℚ × AlgebraicClosure ℚ)) (z : AlgebraicClosure ℚ) :
    σ (Wc.veluX S z) = Wc.veluX (S.image (Prod.map ⇑σ ⇑σ)) (σ z) := by
  have h := map_veluX_finset Wc σ.toAlgHom.toRingHom
    (fun a b hab => σ.injective hab) S z
  rw [hfix] at h
  exact h.symm

private lemma algEquiv_veluY {Wc : WeierstrassCurve (AlgebraicClosure ℚ)}
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hfix : WeierstrassCurve.map Wc σ.toAlgHom.toRingHom = Wc)
    (S : Finset (AlgebraicClosure ℚ × AlgebraicClosure ℚ)) (z w : AlgebraicClosure ℚ) :
    σ (Wc.veluY S z w) = Wc.veluY (S.image (Prod.map ⇑σ ⇑σ)) (σ z) (σ w) := by
  have h := map_veluY_finset Wc σ.toAlgHom.toRingHom
    (fun a b hab => σ.injective hab) S z w
  rw [hfix] at h
  exact h.symm

private lemma smul_some_eq (W₀ : WeierstrassCurve ℚ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {x y : AlgebraicClosure ℚ}
    (h : (WeierstrassCurve.baseChange W₀ (AlgebraicClosure ℚ)).toAffine.Nonsingular x y) :
    ∃ h', (σ • (Point.some x y h :
          (WeierstrassCurve.baseChange W₀ (AlgebraicClosure ℚ)).toAffine.Point))
        = Point.some (σ x) (σ y) h' := by
  rw [algEquiv_smul_def]
  exact ⟨_, Point.map_some _ _⟩

theorem solution (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (L : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hLcard : Nat.card L = p)
    (hLstab : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ L, σ • x ∈ L) :
    ∃ (W' : WeierstrassCurve ℤ)
      (φ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point →+
           ((W'.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point),
      W'.Δ ≠ 0 ∧ φ.ker = L ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
         (x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point),
        φ (σ • x) = σ • φ x) ∧
      (∀ q : ℕ, q.Prime → q ≠ p → (q : ℤ) ∣ W.Δ → ¬ (q : ℤ) ∣ W.c₄ →
        ((q : ℤ) ∣ W'.Δ ∧ ¬ (q : ℤ) ∣ W'.c₄ ∧
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
            ∀ y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
              (W'.InZeroComponentAt A (φ y) ↔
                ∃ k ∈ L, W.InZeroComponentAt A (y - k)))) := by
  classical

  haveI hLfin : Finite L := Nat.finite_of_card_ne_zero (by rw [hLcard]; exact hp.ne_zero)
  haveI hLnontriv : Nontrivial L := by
    rw [← Finite.one_lt_card_iff_nontrivial, hLcard]
    exact hp.one_lt
  obtain ⟨⟨Q, hQL⟩, hQne0⟩ := exists_ne (0 : L)
  have hQordL : addOrderOf (⟨Q, hQL⟩ : L) = p := by
    have hdvd : addOrderOf (⟨Q, hQL⟩ : L) ∣ p := hLcard ▸ addOrderOf_dvd_natCard _
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd) with h1 | hself
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) hQne0
    · exact hself
  have hQord : addOrderOf Q = p := by
    have h := addOrderOf_injective L.subtype L.subtype_injective (⟨Q, hQL⟩ : L)
    rw [show L.subtype (⟨Q, hQL⟩ : L) = Q from rfl] at h
    rw [h, hQordL]
  have hzle : AddSubgroup.zmultiples Q ≤ L := AddSubgroup.zmultiples_le.mpr hQL
  have hzcard : Nat.card (AddSubgroup.zmultiples Q) = p := by
    rw [Nat.card_zmultiples]; exact hQord
  have hzQ : AddSubgroup.zmultiples Q = L := by
    apply SetLike.coe_injective
    refine Set.eq_of_subset_of_ncard_le hzle ?_
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    show Nat.card L ≤ Nat.card (AddSubgroup.zmultiples Q)
    rw [hLcard, hzcard]
  have hQstab : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ • Q ∈ AddSubgroup.zmultiples Q := by
    intro σ
    rw [hzQ]
    exact hLstab σ Q hQL
  have hpn : p = 2 * (p / 2) + 1 := by
    obtain ⟨t, ht⟩ := hp.odd_of_ne_two hp2
    omega

  obtain ⟨W', u, hΔ', hW', e, hue⟩ :=
    WeierstrassCurve.exists_integral_veluQuotient_rescale_of_galois_stable
      W hΔ hp hp2 Q hQord hQstab

  have hΔb : (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)) : WeierstrassCurve _).Δ ≠ 0 := by
    show ((W.map (Int.castRingHom ℚ)).map
      (algebraMap ℚ (AlgebraicClosure ℚ))).Δ ≠ 0
    rw [map_Δ, map_Δ]
    intro hzero
    apply hΔ
    have h1 : ((W.Δ : ℚ) : AlgebraicClosure ℚ) = 0 := by
      rw [← eq_ratCast (algebraMap ℚ (AlgebraicClosure ℚ)) ((W.Δ : ℚ))]
      exact hzero
    have h2 : (W.Δ : ℚ) = 0 := by exact_mod_cast h1
    exact_mod_cast h2
  haveI hWbE : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr hΔb⟩

  obtain ⟨φ₀, hker, hcoord⟩ :=
    WeierstrassCurve.exists_veluPointHom_oddOrderSummingSet_algebraicClosure
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)) hp hp2 Q hQord
  have hW'symm : (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ)) •
      (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluQuotient
        (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (p / 2)))
      = ((W'.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)) := hW'.symm

  have hφker : (AddMonoidHom.comp
      (vcAddEquivOfEq (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ))
        hW'symm).symm.toAddMonoidHom φ₀).ker = L := by
    ext x
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
      EmbeddingLike.map_eq_zero_iff]
    rw [← AddMonoidHom.mem_ker, hker, hzQ]

  have hXc : ∀ z : AlgebraicClosure ℚ,
      vcXInv (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ)) z
        = ((u⁻¹ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ 2 * z := by
    intro z
    rw [show vcXInv (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ)) z
        = ((u⁻¹ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ 2 * (z - 0) from rfl, sub_zero]
  have hYc : ∀ z w : AlgebraicClosure ℚ,
      vcYInv (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ)) z w
        = ((u⁻¹ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ 3 * w := by
    intro z w
    rw [show vcYInv (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ)) z w
        = ((u⁻¹ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ 3 * (w - 0 - 0 * (z - 0))
        from rfl, zero_mul, sub_zero, sub_zero]
  refine ⟨W', _, hΔ', hφker, ?_, ?_⟩

  · intro σ x
    by_cases hxL : x ∈ L
    · have h1 : (AddMonoidHom.comp
          (vcAddEquivOfEq (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ))
            hW'symm).symm.toAddMonoidHom φ₀) x = 0 :=
        AddMonoidHom.mem_ker.mp (by rw [hφker]; exact hxL)
      have h2 : (AddMonoidHom.comp
          (vcAddEquivOfEq (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ))
            hW'symm).symm.toAddMonoidHom φ₀) (σ • x) = 0 :=
        AddMonoidHom.mem_ker.mp (by rw [hφker]; exact hLstab σ x hxL)
      rw [h1, h2]
      have hz : σ • (0 : ((W'.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = 0 := by
        rw [algEquiv_smul_def, Point.map_zero]
      rw [hz]
    · rcases x with _ | ⟨a, b, hab⟩
      · exact absurd (zero_mem L) hxL
      obtain ⟨hab', hsmul⟩ := smul_some_eq (W.map (Int.castRingHom ℚ)) σ hab
      rw [hsmul]
      have hnotz : (Point.some a b hab :
          ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
          ∉ AddSubgroup.zmultiples Q := by rw [hzQ]; exact hxL
      have hσxL : (Point.some (σ a) (σ b) hab' :
          ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) ∉ L := by
        intro hmem
        apply hxL
        have h := hLstab σ⁻¹ _ hmem
        rwa [← hsmul, inv_smul_smul] at h
      have hσnotz : (Point.some (σ a) (σ b) hab' :
          ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
          ∉ AddSubgroup.zmultiples Q := by rw [hzQ]; exact hσxL
      obtain ⟨h₁', hφ₀x⟩ := hcoord a b hab hnotz
      obtain ⟨h₂', hφ₀σx⟩ := hcoord (σ a) (σ b) hab' hσnotz
      obtain ⟨hT1, hTval1⟩ := vcAddEquivOfEq_symm_some_eq
        (C := (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ))) hW'symm h₁'
      obtain ⟨hT2, hTval2⟩ := vcAddEquivOfEq_symm_some_eq
        (C := (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ))) hW'symm h₂'
      have hφx : (AddMonoidHom.comp
          (vcAddEquivOfEq (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ))
            hW'symm).symm.toAddMonoidHom φ₀) (Point.some a b hab) = Point.some _ _ hT1 := by
        rw [AddMonoidHom.comp_apply, hφ₀x]
        rw [show ⇑(vcAddEquivOfEq (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ))
            hW'symm).symm.toAddMonoidHom
          = ⇑(vcAddEquivOfEq (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ))
            hW'symm).symm from rfl]
        exact hTval1
      have hφσx : (AddMonoidHom.comp
          (vcAddEquivOfEq (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ))
            hW'symm).symm.toAddMonoidHom φ₀) (Point.some (σ a) (σ b) hab')
          = Point.some _ _ hT2 := by
        rw [AddMonoidHom.comp_apply, hφ₀σx]
        rw [show ⇑(vcAddEquivOfEq (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ))
            hW'symm).symm.toAddMonoidHom
          = ⇑(vcAddEquivOfEq (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ))
            hW'symm).symm from rfl]
        exact hTval2
      rw [hφσx, hφx]
      obtain ⟨hS1, hsmulT⟩ := smul_some_eq (W'.map (Int.castRingHom ℚ)) σ hT1
      rw [hsmulT]

      have hufix : σ ((u : AlgebraicClosure ℚ)) = (u : AlgebraicClosure ℚ) := by
        rw [hue, map_zpow₀, map_natCast]
      have huinv : σ (((u⁻¹ : (AlgebraicClosure ℚ)ˣ)) : AlgebraicClosure ℚ)
          = ((u⁻¹ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) := by
        rw [Units.val_inv_eq_inv_val, map_inv₀, hufix]
      have hWbfix : WeierstrassCurve.map
          ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)) σ.toAlgHom.toRingHom
          = (W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ) :=
        baseChange_fix (W.map (Int.castRingHom ℚ)) σ
      have hordσ : addOrderOf (σ • Q) = p :=
        (addOrderOf_algEquiv_smul (W.map (Int.castRingHom ℚ)) σ Q).trans hQord
      have himgQ : ((((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet
            Q (p / 2)).image (Prod.map ⇑σ ⇑σ))
          = ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet
            (σ • Q) (p / 2) :=
        image_summingSet_smul (W.map (Int.castRingHom ℚ)) σ Q (p / 2)
      have hXcomm : ∀ z : AlgebraicClosure ℚ,
          σ (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluX
            (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (p / 2)) z)
          = ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluX
            (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (p / 2))
            (σ z) := by
        intro z
        rw [algEquiv_veluX σ hWbfix _ z, himgQ]
        exact veluX_summingSet_congr ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ))
          hp hpn hQord hordσ (hQstab σ) (σ z)
      have hYcomm : ∀ z w : AlgebraicClosure ℚ,
          σ (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluY
            (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (p / 2)) z w)
          = ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluY
            (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (p / 2))
            (σ z) (σ w) := by
        intro z w
        rw [algEquiv_veluY σ hWbfix _ z w, himgQ]
        exact veluY_summingSet_congr ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ))
          hp hpn hQord hordσ (hQstab σ) (σ z) (σ w)
      refine some_eq_some' ?_ ?_
      · rw [hXc, hXc, map_mul, map_pow, huinv, hXcomm]
      · rw [hYc, hYc, map_mul, map_pow, huinv, hYcomm]

  · intro q hq hqp hqΔ hqc₄
    have huk12 : (u : AlgebraicClosure ℚ) ^ 12 = (p : AlgebraicClosure ℚ) ^ (e * 12) := by
      rw [hue, ← zpow_natCast ((p : AlgebraicClosure ℚ) ^ e) 12, ← zpow_mul]
      norm_num
    obtain ⟨hΔ'q, hc₄'q⟩ :=
      WeierstrassCurve.dvd_discriminant_not_dvd_c4_integral_veluQuotient_rescale
        W hΔ hp hp2 Q hQord W' u hW' ⟨e * 12, huk12⟩ hq hqp hqΔ hqc₄
    refine ⟨hΔ'q, hc₄'q, ?_⟩
    intro A hA y
    have hqdvdp : ¬ q ∣ p := fun hd => hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp hd)
    have hvp : A.valuation (p : AlgebraicClosure ℚ) = 1 :=
      ValuationSubring.valuation_natCast_eq_one_of_not_dvd A hq
        (A.mem_nonunits_iff.mp hA) hqdvdp
    have hu1 : A.valuation (u : AlgebraicClosure ℚ) = 1 := by
      rw [hue, map_zpow₀, hvp, one_zpow]
    by_cases hyL : y ∈ L
    · have hφy : (AddMonoidHom.comp
          (vcAddEquivOfEq (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ))
            hW'symm).symm.toAddMonoidHom φ₀) y = 0 :=
        AddMonoidHom.mem_ker.mp (by rw [hφker]; exact hyL)
      rw [hφy]
      exact ⟨fun _ => ⟨y, hyL, by rw [sub_self]; exact Or.inl rfl⟩, fun _ => Or.inl rfl⟩
    · rcases y with _ | ⟨a, b, hab⟩
      · exact absurd (zero_mem L) hyL
      have hnotz : (Point.some a b hab :
          ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
          ∉ AddSubgroup.zmultiples Q := by rw [hzQ]; exact hyL
      obtain ⟨h₁', hφ₀y⟩ := hcoord a b hab hnotz
      obtain ⟨hT1, hTval1⟩ := vcAddEquivOfEq_symm_some_eq
        (C := (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ))) hW'symm h₁'
      have hφy : (AddMonoidHom.comp
          (vcAddEquivOfEq (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ))
            hW'symm).symm.toAddMonoidHom φ₀) (Point.some a b hab) = Point.some _ _ hT1 := by
        rw [AddMonoidHom.comp_apply, hφ₀y]
        rw [show ⇑(vcAddEquivOfEq (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ))
            hW'symm).symm.toAddMonoidHom
          = ⇑(vcAddEquivOfEq (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ))
            hW'symm).symm from rfl]
        exact hTval1
      have hmass : ((W'.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular
          (((u⁻¹ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ 2 *
            ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluX
              (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (p / 2)) a)
          (((u⁻¹ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ 3 *
            ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluY
              (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (p / 2)) a b) := by
        rw [← hXc, ← hYc]
        exact hT1
      rw [hφy, some_eq_some' (h₂ := hmass) (hXc _) (hYc _ _)]
      have hiff := WeierstrassCurve.inZeroComponentAt_veluCoord_iff_of_multiplicative
        W hΔ hp hp2 Q hQord W' u hW' hq hqΔ hqc₄ hΔ'q hc₄'q A hA hu1 a b hab hnotz hmass
      rw [hzQ] at hiff
      exact hiff

end S_WeierstrassCurve_exists_quotientDatum_of_galois_stable_primeCard
end P2MW
export P2MW.S_WeierstrassCurve_exists_quotientDatum_of_galois_stable_primeCard (solution)
