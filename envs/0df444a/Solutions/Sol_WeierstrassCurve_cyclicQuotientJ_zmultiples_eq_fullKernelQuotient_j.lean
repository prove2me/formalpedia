-- Prove2me | solution 1 for WeierstrassCurve.cyclicQuotientJ_zmultiples_eq_fullKernelQuotient_j
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/7c421e5f-ad93-5dd5-b2bf-3389be19dca7

import Mathlib
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import Theorems.Thm_WeierstrassCurve_stepCurve_stepSubgroup_eq_of_prime_ne_two
import Theorems.Thm_WeierstrassCurve_stepCurve_stepSubgroup_two_eq
import Theorems.Thm_WeierstrassCurve_exists_fullKernelHom
import Theorems.Thm_WeierstrassCurve_fullKernelQuotient_discriminant_ne_zero
import Theorems.Thm_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2
import Theorems.Thm_WeierstrassCurve_fullKernelQuotient_fullKernelQuotient_eq_of_fullKernelHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_cyclicQuotientJ_zmultiples_eq_fullKernelQuotient_j
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"

set_option autoImplicit false

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_cyclicQuotientJ_zmultiples_eq_fullKernelQuotient_j.WeierstrassCurve WeierstrassCurve.Affine"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY mk.injEq a₃ a₁ map coe_Δ' mk a₂ Affine.Point.some Affine.negAddY toAffine Affine.Point Affine.addX Δ Affine.addY Affine.Y_eq_of_X_eq Affine.equation_iff j stepCurve stepSubgroup cyclicQuotientCurve cyclicQuotientJ cyclicQuotientJ_def cyclicQuotientCurve_one cyclicQuotientCurve_eq_of_two_le veluGx veluGy veluT veluU veluQuotient veluQuotient2 velu2X velu2Y veluPointMap2 veluPointMap2_some_of_eq veluPointMap2_some_of_ne oddOrderSummingSet fullKernelQuotient fullKernelQuotient_eq_veluQuotient_oddOrderSummingSet fullKernelQuotient_one fullKernelQuotient_two veluX veluY stepCurve_stepSubgroup_eq_of_prime_ne_two stepCurve_stepSubgroup_two_eq exists_fullKernelHom fullKernelQuotient_discriminant_ne_zero exists_addMonoidHom_coe_eq_veluPointMap2 fullKernelQuotient_fullKernelQuotient_eq_of_fullKernelHom"
p2m_open "WeierstrassCurve"

def homOfEq {K : Type*} [Field K] [DecidableEq K] :
    ∀ {W V : WeierstrassCurve K}, W = V → (W.toAffine.Point →+ V.toAffine.Point)
  | _, _, rfl => AddMonoidHom.id _

theorem homOfEq_coordsOrZero {K : Type*} [Field K] [DecidableEq K] {W V : WeierstrassCurve K} (h : W = V)
    (P : W.toAffine.Point) : (homOfEq h P).coordsOrZero = P.coordsOrZero := by
  subst h; rfl

theorem homOfEq_eq_zero_iff {K : Type*} [Field K] [DecidableEq K] {W V : WeierstrassCurve K} (h : W = V)
    (P : W.toAffine.Point) : homOfEq h P = 0 ↔ P = 0 := by
  subst h; rfl

theorem ker_homOfEq_comp {K : Type*} [Field K] [DecidableEq K] {W V U : WeierstrassCurve K} (h : V = U)
    (φ : W.toAffine.Point →+ V.toAffine.Point) : ((homOfEq h).comp φ).ker = φ.ker := by
  subst h; rfl

theorem sigma_homOfEq {K : Type*} [Field K] [DecidableEq K] {W V U : WeierstrassCurve K} (h : V = U)
    (φ : W.toAffine.Point →+ V.toAffine.Point) (H : AddSubgroup W.toAffine.Point) :
    (⟨U, H.map ((homOfEq h).comp φ)⟩ : Σ X : WeierstrassCurve K, AddSubgroup X.toAffine.Point) = ⟨V, H.map φ⟩ := by
  subst h; rfl

section Transport

variable {K : Type*} [Field K] [DecidableEq K]

theorem nsmul_ne_zero_of_pos_of_lt_addOrderOf {W : WeierstrassCurve K} (Q : W.toAffine.Point)
    {N : ℕ} (hQ : addOrderOf Q = N) {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N - 1) :
    k • Q ≠ 0 := by
  intro h
  have hN : 1 ≤ N := le_trans hk1 (le_trans hkN (Nat.sub_le N 1))
  have hdvd : N ∣ k := hQ ▸ addOrderOf_dvd_of_nsmul_eq_zero h
  have hle : N ≤ k := Nat.le_of_dvd hk1 hdvd
  omega

end Transport

section Cleared

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

private theorem _root_.WeierstrassCurve.velu_pair_x_cleared {x y x₀ y₀ : R}
    (hP : W.toAffine.Equation x y) (hR : W.toAffine.Equation x₀ y₀) :
    ((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2 - x₀ * (x - x₀) ^ 2)
      + ((y + y₀ + W.a₁ * x₀ + W.a₃) ^ 2 + W.a₁ * (y + y₀ + W.a₁ * x₀ + W.a₃) * (x - x₀)
          - (W.a₂ + x + x₀) * (x - x₀) ^ 2 - x₀ * (x - x₀) ^ 2)
      = W.veluT x₀ y₀ * (x - x₀) + W.veluU x₀ y₀ := by
  rw [Affine.equation_iff] at hP hR
  simp only [veluT, veluU, veluGx, veluGy]
  linear_combination 2 * hP - 2 * hR

p2m_export "WeierstrassCurve" "velu_pair_x_cleared"

private theorem _root_.WeierstrassCurve.velu_pair_y_cleared {x y x₀ y₀ : R}
    (hP : W.toAffine.Equation x y) (hR : W.toAffine.Equation x₀ y₀) :
    ((-((y - y₀) * (((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2)
            - x * (x - x₀) ^ 2) + y * (x - x₀) ^ 3)
        - W.a₁ * ((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2) * (x - x₀)
        - W.a₃ * (x - x₀) ^ 3) - y₀ * (x - x₀) ^ 3)
      + ((-((y + y₀ + W.a₁ * x₀ + W.a₃) * (((y + y₀ + W.a₁ * x₀ + W.a₃) ^ 2
              + W.a₁ * (y + y₀ + W.a₁ * x₀ + W.a₃) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2)
            - x * (x - x₀) ^ 2) + y * (x - x₀) ^ 3)
        - W.a₁ * ((y + y₀ + W.a₁ * x₀ + W.a₃) ^ 2 + W.a₁ * (y + y₀ + W.a₁ * x₀ + W.a₃) * (x - x₀)
            - (W.a₂ + x + x₀) * (x - x₀) ^ 2) * (x - x₀)
        - W.a₃ * (x - x₀) ^ 3) + (y₀ + W.a₁ * x₀ + W.a₃) * (x - x₀) ^ 3)
      = -(W.veluU x₀ y₀ * (2 * y + W.a₁ * x + W.a₃)
          + W.veluT x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) * (x - x₀)
          + (W.a₁ * W.veluU x₀ y₀ - W.veluGx x₀ y₀ * W.veluGy x₀ y₀) * (x - x₀)) := by
  rw [Affine.equation_iff] at hP hR
  simp only [veluT, veluU, veluGx, veluGy]
  linear_combination (-(2 * y) - 2 * W.a₁ * x + W.a₁ * x₀ - W.a₃) * hP
    + (2 * y + 2 * W.a₁ * x - W.a₁ * x₀ + W.a₃) * hR

p2m_export "WeierstrassCurve" "velu_pair_y_cleared"
end Cleared

section PairField

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

private theorem _root_.WeierstrassCurve.addX_sub_eq_div {x y x₀ y₀ : F} (hd : x - x₀ ≠ 0) :
    W.toAffine.addX x x₀ ((y - y₀) / (x - x₀)) - x₀
      = ((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2 - x₀ * (x - x₀) ^ 2)
          / (x - x₀) ^ 2 := by
  rw [eq_div_iff (pow_ne_zero 2 hd)]
  simp only [Affine.addX]
  field_simp
  ring1

p2m_export "WeierstrassCurve" "addX_sub_eq_div"
private theorem _root_.WeierstrassCurve.addX_neg_sub_eq_div {x y x₀ y₀ : F} (hd : x - x₀ ≠ 0) :
    W.toAffine.addX x x₀ ((y - W.toAffine.negY x₀ y₀) / (x - x₀)) - x₀
      = ((y + y₀ + W.a₁ * x₀ + W.a₃) ^ 2 + W.a₁ * (y + y₀ + W.a₁ * x₀ + W.a₃) * (x - x₀)
          - (W.a₂ + x + x₀) * (x - x₀) ^ 2 - x₀ * (x - x₀) ^ 2) / (x - x₀) ^ 2 := by
  rw [eq_div_iff (pow_ne_zero 2 hd)]
  simp only [Affine.addX, Affine.negY]
  field_simp
  ring1

p2m_export "WeierstrassCurve" "addX_neg_sub_eq_div"
private theorem _root_.WeierstrassCurve.addY_sub_eq_div {x y x₀ y₀ : F} (hd : x - x₀ ≠ 0) :
    W.toAffine.addY x x₀ y ((y - y₀) / (x - x₀)) - y₀
      = ((-((y - y₀) * (((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2)
            - x * (x - x₀) ^ 2) + y * (x - x₀) ^ 3)
        - W.a₁ * ((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2) * (x - x₀)
        - W.a₃ * (x - x₀) ^ 3) - y₀ * (x - x₀) ^ 3) / (x - x₀) ^ 3 := by
  rw [eq_div_iff (pow_ne_zero 3 hd)]
  simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY]
  field_simp
  ring1

p2m_export "WeierstrassCurve" "addY_sub_eq_div"
private theorem _root_.WeierstrassCurve.addY_neg_sub_eq_div {x y x₀ y₀ : F} (hd : x - x₀ ≠ 0) :
    W.toAffine.addY x x₀ y ((y - W.toAffine.negY x₀ y₀) / (x - x₀)) - W.toAffine.negY x₀ y₀
      = ((-((y + y₀ + W.a₁ * x₀ + W.a₃) * (((y + y₀ + W.a₁ * x₀ + W.a₃) ^ 2
              + W.a₁ * (y + y₀ + W.a₁ * x₀ + W.a₃) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2)
            - x * (x - x₀) ^ 2) + y * (x - x₀) ^ 3)
        - W.a₁ * ((y + y₀ + W.a₁ * x₀ + W.a₃) ^ 2 + W.a₁ * (y + y₀ + W.a₁ * x₀ + W.a₃) * (x - x₀)
            - (W.a₂ + x + x₀) * (x - x₀) ^ 2) * (x - x₀)
        - W.a₃ * (x - x₀) ^ 3) + (y₀ + W.a₁ * x₀ + W.a₃) * (x - x₀) ^ 3) / (x - x₀) ^ 3 := by
  rw [eq_div_iff (pow_ne_zero 3 hd)]
  simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY]
  field_simp
  ring1

p2m_export "WeierstrassCurve" "addY_neg_sub_eq_div"
variable [DecidableEq F]

private theorem _root_.WeierstrassCurve.velu_pair {x y x₀ y₀ : F}
    (h : W.toAffine.Nonsingular x y) (h₀ : W.toAffine.Nonsingular x₀ y₀) (hx : x ≠ x₀) :
    (((Point.some x y h + Point.some x₀ y₀ h₀).coordsOrZero.1
          - (Point.some x₀ y₀ h₀ : W.toAffine.Point).coordsOrZero.1)
        + ((Point.some x y h + -Point.some x₀ y₀ h₀).coordsOrZero.1
          - (-(Point.some x₀ y₀ h₀ : W.toAffine.Point)).coordsOrZero.1)
        = W.veluT x₀ y₀ / (x - x₀) + W.veluU x₀ y₀ / (x - x₀) ^ 2) ∧
    (((Point.some x y h + Point.some x₀ y₀ h₀).coordsOrZero.2
          - (Point.some x₀ y₀ h₀ : W.toAffine.Point).coordsOrZero.2)
        + ((Point.some x y h + -Point.some x₀ y₀ h₀).coordsOrZero.2
          - (-(Point.some x₀ y₀ h₀ : W.toAffine.Point)).coordsOrZero.2)
        = -(W.veluU x₀ y₀ * (2 * y + W.a₁ * x + W.a₃) / (x - x₀) ^ 3
            + W.veluT x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) / (x - x₀) ^ 2
            + (W.a₁ * W.veluU x₀ y₀ - W.veluGx x₀ y₀ * W.veluGy x₀ y₀) / (x - x₀) ^ 2)) := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have hP : W.toAffine.Equation x y := h.1
  have hR : W.toAffine.Equation x₀ y₀ := h₀.1
  rw [Point.neg_some h₀, Point.add_of_X_ne hx, Point.add_of_X_ne hx]
  simp only [Point.coordsOrZero_some, slope_of_X_ne hx]
  refine ⟨?_, ?_⟩
  · rw [W.addX_sub_eq_div hd, W.addX_neg_sub_eq_div hd, ← add_div, W.velu_pair_x_cleared hP hR,
      div_add_div _ _ hd (pow_ne_zero 2 hd), div_eq_div_iff (pow_ne_zero 2 hd) (mul_ne_zero hd (pow_ne_zero 2 hd))]
    ring
  · rw [W.addY_sub_eq_div hd, W.addY_neg_sub_eq_div hd, ← add_div, W.velu_pair_y_cleared hP hR, neg_div,
      neg_inj, div_add_div _ _ (pow_ne_zero 3 hd) (pow_ne_zero 2 hd), div_add_div _ _
        (mul_ne_zero (pow_ne_zero 3 hd) (pow_ne_zero 2 hd)) (pow_ne_zero 2 hd),
      div_eq_div_iff (pow_ne_zero 3 hd)
        (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hd) (pow_ne_zero 2 hd)) (pow_ne_zero 2 hd))]
    ring

p2m_export "WeierstrassCurve" "velu_pair"
end PairField

theorem sum_Icc_two_mul_eq_sum_pairs {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 (2 * n), f k = ∑ k ∈ Finset.Icc 1 n, (f k + f (2 * n + 1 - k)) := by
  rw [Finset.sum_add_distrib]
  have hsplit : Finset.Icc 1 (2 * n) = Finset.Icc 1 n ∪ Finset.Icc (n + 1) (2 * n) := by
    ext k; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.Icc 1 n) (Finset.Icc (n + 1) (2 * n)) := by
    rw [Finset.disjoint_left]; intro k hk hk'; simp only [Finset.mem_Icc] at hk hk'; omega
  rw [hsplit, Finset.sum_union hdisj]
  congr 1
  refine Finset.sum_nbij' (fun k => 2 * n + 1 - k) (fun k => 2 * n + 1 - k) ?_ ?_ ?_ ?_ ?_
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk; beta_reduce; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk; beta_reduce; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk; beta_reduce; congr 1; omega

private theorem _root_.WeierstrassCurve.fullKernelPin_eq_veluXY_of_odd
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    (Q : W.toAffine.Point) (n : ℕ) (hQ : addOrderOf Q = 2 * n + 1)
    {x y : F} (h : W.toAffine.Nonsingular x y)
    (hP : (Point.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q) :
    (x + ∑ k ∈ Finset.Icc 1 (2 * n + 1 - 1),
        (((Point.some x y h : W.toAffine.Point) + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
     y + ∑ k ∈ Finset.Icc 1 (2 * n + 1 - 1),
        (((Point.some x y h : W.toAffine.Point) + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)) =
      (W.veluX (W.oddOrderSummingSet Q n) x, W.veluY (W.oddOrderSummingSet Q n) x y) := by
  classical
  have h2n : 2 * n + 1 - 1 = 2 * n := Nat.add_sub_cancel (2 * n) 1
  have hord : (2 * n + 1) • Q = 0 := hQ ▸ addOrderOf_nsmul_eq_zero Q
  have hrefl : ∀ k, k ≤ 2 * n + 1 → (2 * n + 1 - k) • Q = -(k • Q) := by
    intro k hk
    rw [eq_neg_iff_add_eq_zero, ← add_nsmul, Nat.sub_add_cancel hk, hord]

  have haff : ∀ k, 1 ≤ k → k ≤ 2 * n →
      ∃ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀), k • Q = Point.some x₀ y₀ h₀ ∧ x ≠ x₀ := by
    intro k hk1 hk2
    have hne : k • Q ≠ 0 := nsmul_ne_zero_of_pos_of_lt_addOrderOf Q hQ hk1 (by omega)
    rcases hkQ : k • Q with _ | ⟨x₀, y₀, h₀⟩
    · exact absurd hkQ hne
    · refine ⟨x₀, y₀, h₀, rfl, ?_⟩
      intro hxx
      apply hP
      rcases Affine.Y_eq_of_X_eq h.1 h₀.1 hxx with hyy | hyy
      · have hPt : (Point.some x y h : W.toAffine.Point) = k • Q := by
          rw [hkQ]; subst hxx; subst hyy; rfl
        rw [hPt]
        exact AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples Q) k
      · have hPt : (Point.some x y h : W.toAffine.Point) = -(k • Q) := by
          rw [hkQ, Point.neg_some]; subst hxx; subst hyy; rfl
        rw [hPt]
        exact AddSubgroup.neg_mem _ (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples Q) k)

  have hpair : ∀ k ∈ Finset.Icc 1 n,
      ((((Point.some x y h : W.toAffine.Point) + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1)
        + (((Point.some x y h : W.toAffine.Point) + (2 * n + 1 - k) • Q).coordsOrZero.1
            - ((2 * n + 1 - k) • Q).coordsOrZero.1)
        = W.veluT (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2 / (x - (k • Q).coordsOrZero.1)
          + W.veluU (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2 / (x - (k • Q).coordsOrZero.1) ^ 2) ∧
      ((((Point.some x y h : W.toAffine.Point) + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)
        + (((Point.some x y h : W.toAffine.Point) + (2 * n + 1 - k) • Q).coordsOrZero.2
            - ((2 * n + 1 - k) • Q).coordsOrZero.2)
        = -(W.veluU (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2 * (2 * y + W.a₁ * x + W.a₃)
              / (x - (k • Q).coordsOrZero.1) ^ 3
            + W.veluT (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2
              * (W.a₁ * (x - (k • Q).coordsOrZero.1) + y - (k • Q).coordsOrZero.2)
              / (x - (k • Q).coordsOrZero.1) ^ 2
            + (W.a₁ * W.veluU (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2
                - W.veluGx (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2
                  * W.veluGy (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2)
              / (x - (k • Q).coordsOrZero.1) ^ 2)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    obtain ⟨x₀, y₀, h₀, hkQ, hx⟩ := haff k hk.1 (by omega)
    rw [hrefl k (by omega), hkQ]
    exact W.velu_pair h h₀ hx

  have hinj : ∀ k ∈ Finset.Icc 1 n, ∀ k' ∈ Finset.Icc 1 n,
      (k • Q).coordsOrZero = (k' • Q).coordsOrZero → k = k' := by
    intro k hk k' hk' hkk
    rw [Finset.mem_Icc] at hk hk'
    obtain ⟨x₀, y₀, h₀, hkQ, -⟩ := haff k hk.1 (by omega)
    obtain ⟨x₁, y₁, h₁, hk'Q, -⟩ := haff k' hk'.1 (by omega)
    have hpt : k • Q = k' • Q := by
      rw [hkQ, hk'Q] at hkk ⊢
      simp only [Point.coordsOrZero_some, Prod.mk.injEq] at hkk
      obtain ⟨rfl, rfl⟩ := hkk
      rfl
    have hmod := (nsmul_inj_mod (x := Q)).mp hpt
    rwa [hQ, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod

  rw [h2n]
  refine Prod.ext ?_ ?_
  · dsimp only
    rw [sum_Icc_two_mul_eq_sum_pairs, Finset.sum_congr rfl (fun k hk => (hpair k hk).1)]
    simp only [veluX, oddOrderSummingSet, Finset.sum_image hinj]
  · dsimp only
    rw [sum_Icc_two_mul_eq_sum_pairs, Finset.sum_congr rfl (fun k hk => (hpair k hk).2)]
    simp only [veluY, oddOrderSummingSet, Finset.sum_image hinj, Finset.sum_neg_distrib, sub_eq_add_neg]

p2m_export "WeierstrassCurve" "fullKernelPin_eq_veluXY_of_odd"

private theorem _root_.WeierstrassCurve.some_eq_of_X_eq_of_veluGy_eq_zero' {F : Type*} [Field F] (W : WeierstrassCurve F)
    {x₀ y₀ y : F} (h₀ : W.toAffine.Nonsingular x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (h : W.toAffine.Nonsingular x₀ y) :
    (Affine.Point.some x₀ y h : W.toAffine.Point) = Affine.Point.some x₀ y₀ h₀ := by
  have hneg : W.toAffine.negY x₀ y₀ = y₀ := by
    simp only [veluGy] at hgy
    simp only [Affine.negY]
    linear_combination hgy
  have hy : y = y₀ := by
    rcases Affine.Y_eq_of_X_eq h.1 h₀.1 rfl with hy | hy
    · exact hy
    · rw [hy, hneg]
  subst hy
  rfl

p2m_export "WeierstrassCurve" "some_eq_of_X_eq_of_veluGy_eq_zero'"

private theorem _root_.WeierstrassCurve.velu2_translate {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (h2 : (2 : F) ≠ 0) {x y x₀ y₀ : F} (h : W.toAffine.Nonsingular x y) (h₀ : W.toAffine.Nonsingular x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hx : x ≠ x₀) :
    W.velu2X x₀ y₀ x = x + ((Point.some x y h + Point.some x₀ y₀ h₀).coordsOrZero.1 - x₀) ∧
    W.velu2Y x₀ y₀ x y = y + ((Point.some x y h + Point.some x₀ y₀ h₀).coordsOrZero.2 - y₀) := by
  have hnegT : -(Point.some x₀ y₀ h₀ : W.toAffine.Point) = Point.some x₀ y₀ h₀ := by
    rw [Point.neg_some]
    exact W.some_eq_of_X_eq_of_veluGy_eq_zero' h₀ hgy _
  have hp := W.velu_pair h h₀ hx
  rw [hnegT] at hp
  simp only [Point.coordsOrZero_some] at hp
  have hU : W.veluU x₀ y₀ = 0 := by rw [veluU, hgy]; ring
  have hTt : W.veluT x₀ y₀ = 2 * W.veluGx x₀ y₀ := by rw [veluT, hgy]; ring
  rw [hU, hTt, hgy] at hp
  obtain ⟨hp1, hp2⟩ := hp
  have key1 : 2 * ((Point.some x y h + Point.some x₀ y₀ h₀).coordsOrZero.1 - x₀)
      = 2 * (W.veluGx x₀ y₀ / (x - x₀)) := by
    rw [two_mul, hp1]; ring
  have key2 : 2 * ((Point.some x y h + Point.some x₀ y₀ h₀).coordsOrZero.2 - y₀)
      = 2 * (-(W.veluGx x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) / (x - x₀) ^ 2)) := by
    rw [two_mul, hp2]; ring
  refine ⟨?_, ?_⟩
  · rw [mul_left_cancel₀ h2 key1, velu2X]
  · rw [mul_left_cancel₀ h2 key2, velu2Y]; ring

p2m_export "WeierstrassCurve" "velu2_translate"

theorem eq_zero_or_eq_of_veluPointMap2_eq_zero {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}
    (h2 : (2 : F) ≠ 0) {x₀ y₀ : F} (h₀ : W.toAffine.Nonsingular x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)
    (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) (R : W.toAffine.Point)
    (hR : veluPointMap2 h2 h₀.1 hgy hΔ R = 0) :
    R = 0 ∨ R = Point.some x₀ y₀ h₀ := by
  rcases R with _ | ⟨x, y, h⟩
  · exact Or.inl rfl
  · right
    by_cases hx : x = x₀
    · subst hx
      exact W.some_eq_of_X_eq_of_veluGy_eq_zero' h₀ hgy h
    · rw [veluPointMap2_some_of_ne h2 h₀.1 hgy hΔ h hx] at hR
      exact absurd hR (Point.some_ne_zero _)

section Bookkeeping

variable {K : Type*} [Field K] [DecidableEq K]

theorem cqjb_two_torsion_data (W : WeierstrassCurve K) [W.IsElliptic] {m : ℕ} (hm : 0 < m)
    (hN : ((2 * m : ℕ) : K) ≠ 0) (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * m) :
    (2 : K) ≠ 0 ∧ ((m : ℕ) : K) ≠ 0 ∧
    ∃ (x₀ y₀ : K) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      m • Q = Point.some x₀ y₀ h₀ ∧ W.veluGy x₀ y₀ = 0 ∧ (W.veluQuotient2 x₀ y₀).Δ ≠ 0 := by
  have hN' : (2 : K) * (m : K) ≠ 0 := by push_cast at hN; exact hN
  have h2 : (2 : K) ≠ 0 := (mul_ne_zero_iff.mp hN').1
  have hm1 : ((m : ℕ) : K) ≠ 0 := (mul_ne_zero_iff.mp hN').2
  have hT0 : m • Q ≠ 0 := _root_.nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)
  have h2T : 2 • (m • Q) = 0 := by rw [← mul_nsmul', ← hQ, addOrderOf_nsmul_eq_zero]
  obtain ⟨x₀, y₀, h₀, hT⟩ :
      ∃ (x₀ y₀ : K) (h₀ : W.toAffine.Nonsingular x₀ y₀), m • Q = Point.some x₀ y₀ h₀ := by
    rcases hmq : m • Q with _ | ⟨x₀, y₀, h₀⟩
    · exact absurd hmq hT0
    · exact ⟨x₀, y₀, h₀, rfl⟩
  have hgy : W.veluGy x₀ y₀ = 0 := by
    have hneg : -(m • Q) = m • Q := by
      rw [neg_eq_iff_add_eq_zero, ← two_nsmul, h2T]
    rw [hT, Point.neg_some, Point.some.injEq] at hneg
    have hy := hneg.2
    simp only [veluGy, Affine.negY] at hy ⊢
    linear_combination hy
  have hΔ₂ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0 := by
    have hT2 : addOrderOf (m • Q) = 2 := addOrderOf_eq_prime h2T hT0
    have h2n : ((2 : ℕ) : K) ≠ 0 := by exact_mod_cast h2
    have hD := fullKernelQuotient_discriminant_ne_zero 2 W h2n (m • Q) hT2
    rwa [hT, fullKernelQuotient_two W h₀ hgy] at hD
  exact ⟨h2, hm1, x₀, y₀, h₀, hT, hgy, hΔ₂⟩

omit [Field K] [DecidableEq K] in

theorem cqjb_mem_zmultiples_of_addOrderOf_eq_two {A : Type*} [AddCommGroup A] {T : A} (hT : addOrderOf T = 2)
    (P : A) : P ∈ AddSubgroup.zmultiples T ↔ P = 0 ∨ P = T := by
  have h2T : (2 : ℤ) • T = 0 := by
    have h := addOrderOf_nsmul_eq_zero T
    rw [hT] at h
    exact_mod_cast h
  constructor
  · rintro ⟨k, rfl⟩
    rcases Int.even_or_odd' k with ⟨j, rfl | rfl⟩
    · left
      show (2 * j) • T = 0
      rw [mul_comm, mul_zsmul, h2T, zsmul_zero]
    · right
      show (2 * j + 1) • T = T
      rw [add_zsmul, mul_comm, mul_zsmul, h2T, zsmul_zero, one_zsmul, zero_add]
  · rintro (rfl | rfl)
    · exact zero_mem _
    · exact AddSubgroup.mem_zmultiples _

omit [Field K] [DecidableEq K] in

theorem cqjb_addOrderOf_map_eq {A B : Type*} [AddCommGroup A] [AddCommGroup B] (φ : A →+ B) {Q : A}
    {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (hQ : addOrderOf Q = d * m)
    (hker : φ.ker = AddSubgroup.zmultiples (m • Q)) : addOrderOf (φ Q) = m := by
  apply Nat.dvd_antisymm
  · apply addOrderOf_dvd_of_nsmul_eq_zero
    have h : φ (m • Q) = 0 := by
      rw [← AddMonoidHom.mem_ker, hker]; exact AddSubgroup.mem_zmultiples _
    rwa [map_nsmul] at h
  · set k := addOrderOf (φ Q) with hk
    have h0 : φ (k • Q) = 0 := by rw [map_nsmul, hk, addOrderOf_nsmul_eq_zero]
    have hmem : k • Q ∈ AddSubgroup.zmultiples (m • Q) := by rw [← hker, AddMonoidHom.mem_ker]; exact h0
    obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    have hzs : ((k : ℤ) - z * m) • Q = 0 := by
      rw [sub_zsmul, natCast_zsmul, mul_zsmul, natCast_zsmul, hz]; abel
    have hdvd : ((d * m : ℕ) : ℤ) ∣ (k : ℤ) - z * m := by
      have h := (addOrderOf_dvd_iff_zsmul_eq_zero).mpr hzs
      rwa [hQ] at h
    have hmdvd : (m : ℤ) ∣ (k : ℤ) - z * m := by
      refine dvd_trans ?_ hdvd
      exact ⟨d, by push_cast; ring⟩
    have : (m : ℤ) ∣ (k : ℤ) := by
      have := dvd_add hmdvd (dvd_mul_left (m : ℤ) z)
      rwa [sub_add_cancel] at this
    exact_mod_cast this

theorem cqjb_addOrderOf_nsmul {A : Type*} [AddCommGroup A] {Q : A} {d m : ℕ} (hm : 0 < m)
    (hQ : addOrderOf Q = d * m) : addOrderOf (m • Q) = d := by
  rw [addOrderOf_nsmul_of_dvd (by omega) (by rw [hQ]; exact dvd_mul_left m d), hQ, Nat.mul_div_cancel d hm]

end Bookkeeping

section Step

variable {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]

theorem cqjb_step_data (W : WeierstrassCurve K) [W.IsElliptic] {d m : ℕ} (hdp : d.Prime) (hm : 0 < m)
    (hN : ((d * m : ℕ) : K) ≠ 0) (Q : W.toAffine.Point) (hQ : addOrderOf Q = d * m) :
    ∃ φ : W.toAffine.Point →+ (W.fullKernelQuotient (m • Q) d).toAffine.Point,
      φ.ker = AddSubgroup.zmultiples (m • Q) ∧
      (∀ P : W.toAffine.Point, P ∉ AddSubgroup.zmultiples (m • Q) →
        (φ P).coordsOrZero =
          (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (d - 1),
              ((P + k • (m • Q)).coordsOrZero.1 - (k • (m • Q)).coordsOrZero.1),
           P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (d - 1),
              ((P + k • (m • Q)).coordsOrZero.2 - (k • (m • Q)).coordsOrZero.2))) ∧
      (⟨W.stepCurve (AddSubgroup.zmultiples Q) d, W.stepSubgroup (AddSubgroup.zmultiples Q) d⟩ :
          Σ V : WeierstrassCurve K, AddSubgroup V.toAffine.Point) =
        ⟨W.fullKernelQuotient (m • Q) d, (AddSubgroup.zmultiples Q).map φ⟩ := by
  classical
  have hd0 : 0 < d := hdp.pos
  have hdK : (d : K) ≠ 0 := by
    intro h; apply hN; push_cast; rw [h, zero_mul]
  have hmK : (m : K) ≠ 0 := by
    intro h; apply hN; push_cast; rw [h, mul_zero]
  haveI : NeZero d := ⟨hdp.ne_zero⟩
  have hT : addOrderOf (m • Q) = d := cqjb_addOrderOf_nsmul hm hQ
  have hTQ : m • Q ∈ AddSubgroup.zmultiples Q := AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples Q) m

  haveI : IsAddCyclic (AddSubgroup.zmultiples Q) := inferInstance
  haveI : Finite (AddSubgroup.zmultiples Q) := by
    apply Nat.finite_of_card_ne_zero
    rw [Nat.card_zmultiples, hQ]; positivity
  by_cases hd2 : d = 2
  ·
    subst hd2
    obtain ⟨h2, -, x₀, y₀, h₀, hTeq, hgy, hΔ₂⟩ := cqjb_two_torsion_data W hm hN Q hQ
    obtain ⟨φ₂, hφ₂⟩ := W.exists_addMonoidHom_coe_eq_veluPointMap2 h2 h₀.1 hgy hΔ₂
    have e : W.veluQuotient2 x₀ y₀ = W.fullKernelQuotient (m • Q) 2 := by
      rw [hTeq]; exact (fullKernelQuotient_two W h₀ hgy).symm
    refine ⟨(homOfEq e).comp φ₂, ?_, ?_, ?_⟩
    ·
      rw [ker_homOfEq_comp]
      ext P
      rw [AddMonoidHom.mem_ker, cqjb_mem_zmultiples_of_addOrderOf_eq_two hT, hφ₂]
      constructor
      · intro hP
        rcases eq_zero_or_eq_of_veluPointMap2_eq_zero h2 h₀ hgy hΔ₂ P hP with h | h
        · exact Or.inl h
        · exact Or.inr (h.trans hTeq.symm)
      · rintro (rfl | rfl)
        · rfl
        · rw [hTeq]; exact veluPointMap2_some_of_eq h2 h₀.1 hgy hΔ₂ h₀ rfl
    ·
      intro P hP
      rw [cqjb_mem_zmultiples_of_addOrderOf_eq_two hT, not_or] at hP
      obtain ⟨hP0, hPT⟩ := hP
      rcases P with _ | ⟨x, y, h⟩
      · exact absurd rfl hP0
      · have hx : x ≠ x₀ := by
          intro hx; apply hPT; rw [hTeq]; subst hx
          exact W.some_eq_of_X_eq_of_veluGy_eq_zero' h₀ hgy h
        rw [AddMonoidHom.comp_apply, homOfEq_coordsOrZero, hφ₂, veluPointMap2_some_of_ne h2 h₀.1 hgy hΔ₂ h hx]
        simp only [show (2 : ℕ) - 1 = 1 from rfl, Finset.Icc_self, Finset.sum_singleton, one_nsmul, hTeq,
          Point.coordsOrZero_some]
        obtain ⟨h1, h2'⟩ := W.velu2_translate h2 h h₀ hgy hx
        rw [h1, h2']
    ·
      rw [W.stepCurve_stepSubgroup_two_eq h2 (AddSubgroup.zmultiples Q) h₀ (hTeq ▸ hTQ) hgy hΔ₂ φ₂ hφ₂]
      exact (sigma_homOfEq e φ₂ (AddSubgroup.zmultiples Q)).symm
  ·
    obtain ⟨n, hn⟩ : ∃ n, d = 2 * n + 1 := hdp.odd_of_ne_two hd2
    have hn2 : d / 2 = n := by omega
    obtain ⟨φ, hker, hpin⟩ := W.exists_fullKernelHom hdK (m • Q) hT
    refine ⟨φ, hker, hpin, ?_⟩
    have hTn : addOrderOf (m • Q) = 2 * n + 1 := hn ▸ hT
    have e : W.fullKernelQuotient (m • Q) d = W.veluQuotient (W.oddOrderSummingSet (m • Q) (d / 2)) := by
      rw [hn2, hn]
      exact fullKernelQuotient_eq_veluQuotient_oddOrderSummingSet W (m • Q) n hTn
    set φᵥ := (homOfEq e).comp φ with hφᵥ
    have hkerᵥ : φᵥ.ker = AddSubgroup.zmultiples (m • Q) := by rw [hφᵥ, ker_homOfEq_comp, hker]
    have hvelu : ∀ (x y : K) (h : W.toAffine.Nonsingular x y),
        (.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples (m • Q) →
          ∃ h', φᵥ (.some x y h) = .some (W.veluX (W.oddOrderSummingSet (m • Q) (d / 2)) x)
            (W.veluY (W.oddOrderSummingSet (m • Q) (d / 2)) x y) h' := by
      intro x y h hP
      have hne : φ (.some x y h) ≠ 0 := by
        intro h0; apply hP; rw [← hker, AddMonoidHom.mem_ker]; exact h0
      have hc := hpin (.some x y h) hP
      have hv := W.fullKernelPin_eq_veluXY_of_odd (m • Q) n hTn h hP
      rw [← hn, ← hn2] at hv
      simp only [Point.coordsOrZero_some] at hc
      rcases hφP : φᵥ (.some x y h) with _ | ⟨X, Y, hXY⟩
      · exfalso
        rw [hφᵥ, AddMonoidHom.comp_apply] at hφP
        exact hne ((homOfEq_eq_zero_iff e _).mp hφP)
      · have hcoords : (X, Y) = (W.veluX (W.oddOrderSummingSet (m • Q) (d / 2)) x,
            W.veluY (W.oddOrderSummingSet (m • Q) (d / 2)) x y) := by
          rw [← hv, ← hc, ← Point.coordsOrZero_some hXY, ← hφP, hφᵥ, AddMonoidHom.comp_apply,
            homOfEq_coordsOrZero]
        simp only [Prod.mk.injEq] at hcoords
        obtain ⟨rfl, rfl⟩ := hcoords
        exact ⟨hXY, rfl⟩
    rw [W.stepCurve_stepSubgroup_eq_of_prime_ne_two hdp hd2 (AddSubgroup.zmultiples Q) (m • Q) hTQ hT φᵥ hkerᵥ hvelu]
    exact sigma_homOfEq e φ (AddSubgroup.zmultiples Q)

theorem cqjb_cyclicQuotientCurve_eq (N : ℕ) :
    ∀ (W : WeierstrassCurve K) [W.IsElliptic] (Q : W.toAffine.Point), (N : K) ≠ 0 → addOrderOf Q = N →
      W.cyclicQuotientCurve (AddSubgroup.zmultiples Q) N = W.fullKernelQuotient Q N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro W _ Q hNK hQ
  rcases Nat.lt_or_ge N 2 with hN2 | hN2
  · interval_cases N
    · exact absurd Nat.cast_zero hNK
    · rw [cyclicQuotientCurve_one, fullKernelQuotient_one]
  ·
    obtain ⟨m, hdm⟩ := Nat.minFac_dvd N
    have hdp : (N.minFac).Prime := Nat.minFac_prime (by omega)
    set d := N.minFac with hd
    have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, mul_zero] at hdm; omega
      · exact h
    have hmN : m < N := by
      rw [hdm]
      exact lt_mul_of_one_lt_left hm hdp.one_lt
    rw [cyclicQuotientCurve_eq_of_two_le W (AddSubgroup.zmultiples Q) hN2, ← hd]
    have hdiv : N / d = m := by rw [hdm, Nat.mul_div_cancel_left m hdp.pos]
    rw [hdiv]
    rw [hdm] at hNK hQ
    obtain ⟨φ, hker, hpin, hsig⟩ := cqjb_step_data W hdp hm hNK Q hQ
    have hstep := congrArg
      (fun s : (Σ V : WeierstrassCurve K, AddSubgroup V.toAffine.Point) => s.1.cyclicQuotientCurve s.2 m) hsig
    simp only at hstep
    rw [hstep, AddMonoidHom.map_zmultiples]
    have hdK : (d : K) ≠ 0 := by
      intro h; apply hNK; push_cast; rw [h, zero_mul]
    have hmK : (m : K) ≠ 0 := by
      intro h; apply hNK; push_cast; rw [h, mul_zero]
    have hT : addOrderOf (m • Q) = d := cqjb_addOrderOf_nsmul hm hQ
    haveI : (W.fullKernelQuotient (m • Q) d).IsElliptic :=
      ⟨isUnit_iff_ne_zero.mpr (fullKernelQuotient_discriminant_ne_zero d W hdK (m • Q) hT)⟩
    haveI : NeZero d := ⟨hdp.ne_zero⟩
    haveI : NeZero m := ⟨by omega⟩
    rw [ih m hmN (W.fullKernelQuotient (m • Q) d) (φ Q) hmK (cqjb_addOrderOf_map_eq φ hdp.pos hm hQ hker),
      W.fullKernelQuotient_fullKernelQuotient_eq_of_fullKernelHom hNK Q hQ φ hker hpin, ← hdm]

end Step

end WeierstrassCurve

theorem solution
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic] (Q : W.toAffine.Point) (hQ : addOrderOf Q = N)
    (hΔ : (W.fullKernelQuotient Q N).Δ ≠ 0) :
    W.cyclicQuotientJ (AddSubgroup.zmultiples Q) N =
      @WeierstrassCurve.j K _ (W.fullKernelQuotient Q N) ⟨isUnit_iff_ne_zero.mpr hΔ⟩ := by
  rw [cyclicQuotientJ_def, WeierstrassCurve.cqjb_cyclicQuotientCurve_eq N W Q hN hQ, WeierstrassCurve.j,
    div_eq_mul_inv, mul_comm, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']

end S_WeierstrassCurve_cyclicQuotientJ_zmultiples_eq_fullKernelQuotient_j
end P2MW
export P2MW.S_WeierstrassCurve_cyclicQuotientJ_zmultiples_eq_fullKernelQuotient_j (solution)
