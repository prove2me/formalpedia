-- Prove2me | solution 1 for WeierstrassCurve.exists_supersingular_endomorphism_natCard_ker_eq_odd_pow_stabilizing_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/add72a9c-c25b-5142-95a9-55104fde1844

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_DualIsogenyAPI
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_Polynomial_DeuringPolynomial
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_Polynomial_eval_zero_deuringPolynomial_map
import Theorems.Thm_Polynomial_eval_one_deuringPolynomial_map
import Theorems.Thm_Polynomial_natDegree_deuringPolynomial_map
import Theorems.Thm_WeierstrassCurve_forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_of_lt_five
import Theorems.Thm_WeierstrassCurve_exists_isDefiniteRamifiedExactlyAt_isMaximalOrder_range_eq_rationalEndSubring
import Theorems.Thm_QuaternionAlgebra_exists_isQuadraticDatum_of_sq_lt_four_mul_of_not_isSquare_padic
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_sub_smul_id_eq_char_smul_of_dvd_of_sq_dvd
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_comp_self_add_smul_eq_smul_of_natCast_mul
import Theorems.Thm_AddMonoidHom_exists_isAddCyclic_natCard_eq_forall_apply_mem_of_apply_apply_eq_smul
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_apply_map_eq_map_apply
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_isDualPair_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_isAddCyclic_ker_and_card_ker_eq_of_comp_self_add_smul_eq_smul
import Theorems.Thm_WeierstrassCurve_j_mem_ssJSet_of_forall_smul_eq_zero
import Theorems.Thm_ModularCurve_mem_ssJSet_map_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_neg_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_supersingular_endomorphism_natCard_ker_eq_odd_pow_stabilizing_cyclic
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.Point.instFinite WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion"
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star"
p2m_attr_erase "simp" "TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero FrobeniusEndo.linePencil_apply WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.frobPoint_zero WeierstrassCurve.frobCardHom_apply WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.pointAddEquivOfEq_refl AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply"
p2m_attr_erase "simp" "ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit"

set_option autoImplicit false

open scoped Quaternion

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map_map map b₂ twoTorsionPolynomial map_j ofJ_j Affine.Point.map_injective ofJ toAffine Affine.Point map_injective Affine.Point.map b₆ b₈ Δ baseChange j b₄ evalEvalBC rationalHomSet rationalEndSubring zero_mem_rationalHomSet id_mem_rationalHomSet hasseInvariant legendreCurve forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero exists_isDefiniteRamifiedExactlyAt_isMaximalOrder_range_eq_rationalEndSubring exists_mem_rationalHomSet_sub_smul_id_eq_char_smul_of_dvd_of_sq_dvd exists_mem_rationalHomSet_comp_self_add_smul_eq_smul_of_natCast_mul nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed exists_mem_rationalHomSet_apply_map_eq_map_apply card_torsion_of_isAlgClosed exists_isDualPair_of_mem_rationalHomSet isAddCyclic_ker_and_card_ker_eq_of_comp_self_add_smul_eq_smul j_mem_ssJSet_of_forall_smul_eq_zero add_mem_rationalHomSet neg_mem_rationalHomSet comp_mem_rationalHomSet"
namespace OddPowSupersingularPort
p2m_open "WeierstrassCurve~card"

section Arith

open Finset

theorem exists_not_isSquare_sq_sub {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (c : ZMod p) (hc : c ≠ 0) :
    ∃ r : ZMod p, ¬ IsSquare (r ^ 2 - c) := by
  by_contra h
  push Not at h
  have step : ∀ (k : ℕ) (y : ZMod p), IsSquare y → IsSquare (y - k • c) := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      obtain ⟨r, hr⟩ := ih y hy
      have : y - (k + 1) • c = r ^ 2 - c := by rw [add_smul, one_smul, ← sub_sub, hr, sq]
      rw [this]
      exact h r
  have hall : ∀ z : ZMod p, IsSquare z := by
    intro z
    have hk : ((((-z) * c⁻¹).val : ℕ) : ZMod p) * c = -z := by
      rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hc, mul_one]
    have := step (((-z) * c⁻¹).val) 0 ⟨0, by simp⟩
    rwa [nsmul_eq_mul, hk, zero_sub, neg_neg] at this
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  exact ha (hall a)

theorem not_isSquare_padic_of_map {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] (π : ℤ_[p] →+* R)
    (z : ℤ) (hz : ¬ (p : ℤ) ∣ z) (h : ¬ IsSquare ((z : R))) : ¬ IsSquare ((z : ℚ_[p])) := by
  rintro ⟨y, hy⟩
  have hz1 : ‖(z : ℚ_[p])‖ = 1 := by
    apply le_antisymm (Padic.norm_int_le_one z)
    by_contra hlt
    exact hz (Padic.norm_intCast_lt_one_iff.mp (not_le.mp hlt))
  have hy1 : ‖y‖ = 1 := by
    have h2 : ‖y‖ * ‖y‖ = 1 := by rw [← norm_mul, ← hy, hz1]
    have h0 : 0 ≤ ‖y‖ := norm_nonneg y
    nlinarith [h2, h0]
  set y' : ℤ_[p] := ⟨y, hy1.le⟩ with hy'
  have hzy : (z : ℤ_[p]) = y' * y' := by
    apply Subtype.ext
    rw [PadicInt.coe_intCast, hy]
    rfl
  apply h
  refine ⟨π y', ?_⟩
  rw [← map_mul, ← hzy, map_intCast]

theorem exists_params (p s M : ℕ) [hp : Fact p.Prime] (hs : s.Prime) (hsp : s ≠ p) (hM : M ≠ 0)
    (hpM : ¬ p ∣ M) (hsM : ¬ s ∣ M) :
    ∃ (n m : ℕ) (t₁ n₂ : ℤ), Odd n ∧ 0 < m ∧
      (1 : ℤ) + m * t₁ + (m : ℤ) ^ 2 * (M * n₂) = (s : ℤ) ^ n ∧
      IsCoprime t₁ (M : ℤ) ∧
      (2 + (m : ℤ) * t₁) ^ 2 < 4 * (s : ℤ) ^ n ∧
      ¬ (s : ℤ) ∣ 2 + (m : ℤ) * t₁ ∧
      ¬ IsSquare (((2 + (m : ℤ) * t₁) ^ 2 - 4 * (s : ℤ) ^ n : ℤ) : ℚ_[p]) := by
  have hpp := hp.out
  have hs2 : 2 ≤ s := hs.two_le
  have hs1 : s - 1 ≠ 0 := by omega

  set e := (s - 1).factorization p with he
  set m := (s - 1) / p ^ e with hm
  have hpem : p ^ e * m = s - 1 := Nat.ordProj_mul_ordCompl_eq_self (s - 1) p
  have hm0 : 0 < m := Nat.ordCompl_pos p hs1
  have hpm : ¬ p ∣ m := Nat.not_dvd_ordCompl hpp hs1

  have cop_sM : s.Coprime M := (Nat.Prime.coprime_iff_not_dvd hs).mpr hsM
  have cop_pM : p.Coprime M := (Nat.Prime.coprime_iff_not_dvd hpp).mpr hpM
  have cop_ps : p.Coprime s := (Nat.coprime_primes hpp hs).mpr (Ne.symm hsp)
  have cop_pm : p.Coprime m := (Nat.Prime.coprime_iff_not_dvd hpp).mpr hpm
  have cop_ss1 : s.Coprime (s - 1) := by
    have : s = (s - 1) + 1 := by omega
    conv_lhs => rw [this]
    rw [Nat.coprime_self_add_left]
    exact Nat.coprime_one_left _
  have cop_sm : s.Coprime m := cop_ss1.coprime_dvd_right ⟨p ^ e, by rw [mul_comm, hpem]⟩
  have cop_s : s.Coprime ((s - 1) * M) := Nat.Coprime.mul_right cop_ss1 cop_sM

  set L := Nat.totient ((s - 1) * M) with hL
  have hL0 : 0 < L := Nat.totient_pos.mpr (Nat.mul_pos (Nat.pos_of_ne_zero hs1) (Nat.pos_of_ne_zero hM))
  set D := m ^ 2 * M with hD
  have hD0 : 0 < D := Nat.mul_pos (pow_pos hm0 2) (Nat.pos_of_ne_zero hM)
  set K₀ := D * (p * s) with hK₀
  set k := L * K₀ with hk
  set n := 2 * k + 1 with hn

  have hcong : (s - 1) * M ∣ s ^ (2 * k) - 1 := by
    have h1 : s ^ L ≡ 1 [MOD (s - 1) * M] := Nat.ModEq.pow_totient cop_s
    have h2 : s ^ (2 * k) ≡ 1 [MOD (s - 1) * M] := by
      have := h1.pow (2 * K₀)
      rwa [one_pow, ← pow_mul, show L * (2 * K₀) = 2 * k by rw [hk]; ring] at this
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hs.pos)).mp h2.symm
  obtain ⟨w, hw⟩ := hcong
  have hwZ : (s : ℤ) ^ (2 * k) - 1 = ((s : ℤ) - 1) * M * w := by
    have h1 : ((s ^ (2 * k) - 1 : ℕ) : ℤ) = (((s - 1) * M * w : ℕ) : ℤ) := by rw [hw]
    push_cast [Nat.one_le_pow _ _ hs.pos, hs.one_le] at h1
    exact h1

  set G₂ : ℤ := ∑ i ∈ range (2 * k), (s : ℤ) ^ i with hG₂
  set u₀ : ℤ := ∑ i ∈ range (2 * k + 1), (s : ℤ) ^ i with hu₀
  have hs1Z : (s : ℤ) - 1 ≠ 0 := by
    have : (2 : ℤ) ≤ s := by exact_mod_cast hs2
    omega
  have hG₂w : G₂ = M * w := by
    have h1 : G₂ * ((s : ℤ) - 1) = (M * w) * ((s : ℤ) - 1) := by
      rw [hG₂, geom_sum_mul, hwZ]; ring
    exact mul_right_cancel₀ hs1Z h1
  have hu₀G : u₀ = s * G₂ + 1 := by rw [hu₀, hG₂, geom_sum_succ]
  have hu₀s : u₀ * ((s : ℤ) - 1) = (s : ℤ) ^ n - 1 := by rw [hu₀, geom_sum_mul, hn]

  have hgood : ∃ rp : ℕ, ∀ t : ℤ, (t : ZMod p) = (rp : ZMod p) →
      ¬ IsSquare (((t ^ 2 - 4 * (s : ℤ) ^ n : ℤ)) : ℚ_[p]) := by
    by_cases hp2 : p = 2
    · subst hp2
      refine ⟨1, fun t ht => ?_⟩
      have hsodd : Odd s := hs.odd_of_ne_two hsp
      have htodd : Odd t := by
        refine Int.not_even_iff_odd.mp ?_
        rw [even_iff_two_dvd]
        intro h2
        have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd t 2).mpr h2
        rw [Nat.cast_one] at ht
        rw [ht] at h0
        exact one_ne_zero h0
      obtain ⟨a, ha⟩ := htodd
      obtain ⟨b, hb⟩ := (hsodd.pow (n := n))
      have hΔ8 : (((t ^ 2 - 4 * (s : ℤ) ^ n : ℤ)) : ZMod (2 ^ 3)) = 5 := by
        have hb' : ((s : ℤ) ^ n) = 2 * (b : ℤ) + 1 := by exact_mod_cast hb
        rw [ha, hb']
        push_cast
        have key : ∀ x y : ZMod (2 ^ 3), (2 * x + 1) ^ 2 - 4 * (2 * y + 1) = 5 := by decide
        exact key _ _
      refine not_isSquare_padic_of_map (PadicInt.toZModPow 3) _ ?_ ?_
      · rw [ha]
        rintro ⟨c, hc⟩
        push_cast at hc
        have : (2 * a + 1) ^ 2 - 4 * (s : ℤ) ^ n = 2 * (2 * a ^ 2 + 2 * a - 2 * (s : ℤ) ^ n) + 1 := by ring
        omega
      · rw [hΔ8]
        have key : ∀ x : ZMod (2 ^ 3), 5 ≠ x * x := by decide
        rintro ⟨x, hx⟩
        exact key x hx
    · have h4 : (4 : ZMod p) ≠ 0 := by
        intro h
        have : ((4 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
        rw [ZMod.natCast_eq_zero_iff] at this
        have := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp
          (hpp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using this))
        exact hp2 this
      have hsZ : (s : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact fun h => hsp ((Nat.prime_dvd_prime_iff_eq hpp hs).mp h).symm
      obtain ⟨r, hr⟩ := exists_not_isSquare_sq_sub hp2 (4 * (s : ZMod p) ^ n)
        (mul_ne_zero h4 (pow_ne_zero _ hsZ))
      refine ⟨r.val, fun t ht => ?_⟩
      rw [ZMod.natCast_zmod_val] at ht
      have hΔp : (((t ^ 2 - 4 * (s : ℤ) ^ n : ℤ)) : ZMod p) = r ^ 2 - 4 * (s : ZMod p) ^ n := by
        push_cast; rw [ht]
      refine not_isSquare_padic_of_map (PadicInt.toZMod) _ ?_ ?_
      · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hΔp]
        rintro h0
        apply hr
        rw [h0]; exact ⟨0, by simp⟩
      · rwa [hΔp]
  obtain ⟨rp, hrp⟩ := hgood

  have hp0 : p ≠ 0 := hpp.ne_zero
  have hs0 : s ≠ 0 := hs.ne_zero
  set r₀ := Nat.chineseRemainder cop_ps rp 1 with hr₀
  have cop_D : D.Coprime (p * s) := by
    rw [hD]
    refine Nat.Coprime.mul_left (Nat.Coprime.pow_left 2 ?_) ?_
    · exact Nat.Coprime.mul_right cop_pm.symm cop_sm.symm
    · exact Nat.Coprime.mul_right cop_pM.symm cop_sM.symm
  set X : ℕ := 1 + s ^ n with hX
  set t₀ := Nat.chineseRemainder cop_D X (r₀ : ℕ) with ht₀
  have ht₀lt : (t₀ : ℕ) < D * (p * s) := Nat.chineseRemainder_lt_mul cop_D X r₀ hD0.ne' (mul_ne_zero hp0 hs0)
  have ht₀D : (t₀ : ℕ) ≡ X [MOD D] := t₀.2.1
  have ht₀ps : (t₀ : ℕ) ≡ (r₀ : ℕ) [MOD p * s] := t₀.2.2
  have ht₀p : (t₀ : ℕ) ≡ rp [MOD p] := (Nat.ModEq.of_mul_right s ht₀ps).trans r₀.2.1
  have ht₀s : (t₀ : ℕ) ≡ 1 [MOD s] := (Nat.ModEq.of_mul_left p ht₀ps).trans r₀.2.2

  obtain ⟨n₂, hn₂⟩ : (D : ℤ) ∣ (X : ℤ) - (t₀ : ℕ) := (Nat.modEq_iff_dvd.mp ht₀D)

  set t₁ : ℤ := (p : ℤ) ^ e * u₀ - m * M * n₂ with ht₁
  have hpemZ : (p : ℤ) ^ e * m = s - 1 := by
    have : ((p ^ e * m : ℕ) : ℤ) = ((s - 1 : ℕ) : ℤ) := by rw [hpem]
    push_cast [hs.one_le] at this
    exact this
  have htt₀ : (2 : ℤ) + m * t₁ = ((t₀ : ℕ) : ℤ) := by
    have hX' : ((X : ℕ) : ℤ) = 1 + (s : ℤ) ^ n := by rw [hX]; push_cast; ring
    have hD' : ((D : ℕ) : ℤ) = (m : ℤ) ^ 2 * M := by rw [hD]; push_cast; ring
    rw [hX', hD'] at hn₂
    have : ((t₀ : ℕ) : ℤ) = 1 + (s : ℤ) ^ n - (m : ℤ) ^ 2 * M * n₂ := by linear_combination -hn₂
    rw [this, ht₁]
    linear_combination u₀ * hpemZ + hu₀s
  refine ⟨n, m, t₁, n₂, ⟨k, hn⟩, hm0, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [ht₁]
    linear_combination u₀ * hpemZ + hu₀s
  ·
    have hcopZ : IsCoprime ((p : ℤ) ^ e) (M : ℤ) := by
      have := (Nat.Coprime.pow_left e cop_pM).isCoprime
      exact_mod_cast this
    have : t₁ = (p : ℤ) ^ e + (M : ℤ) * ((p : ℤ) ^ e * s * w - m * n₂) := by
      rw [ht₁, hu₀G, hG₂w]; ring
    rw [this]
    exact hcopZ.add_mul_left_left _
  ·
    rw [htt₀]
    have h1 : (t₀ : ℕ) < s ^ k := by
      calc (t₀ : ℕ) < D * (p * s) := ht₀lt
        _ = K₀ := by rw [hK₀]
        _ < s ^ K₀ := Nat.lt_pow_self hs.one_lt
        _ ≤ s ^ k := Nat.pow_le_pow_right hs.pos (by rw [hk]; exact Nat.le_mul_of_pos_left K₀ hL0)
    have h2 : (t₀ : ℕ) ^ 2 < 4 * s ^ n := by
      calc (t₀ : ℕ) ^ 2 < (s ^ k) ^ 2 := Nat.pow_lt_pow_left h1 two_ne_zero
        _ = s ^ (2 * k) := by rw [← pow_mul, mul_comm]
        _ ≤ s ^ n := Nat.pow_le_pow_right hs.pos (by rw [hn]; omega)
        _ ≤ 4 * s ^ n := Nat.le_mul_of_pos_left _ (by norm_num)
    exact_mod_cast h2
  ·
    rw [htt₀, Int.natCast_dvd_natCast]
    intro hdvd
    have h1 : (t₀ : ℕ) % s = 1 := by rw [ht₀s, Nat.mod_eq_of_lt hs.one_lt]
    rw [Nat.mod_eq_zero_of_dvd hdvd] at h1
    exact zero_ne_one h1
  ·
    rw [htt₀]
    apply hrp
    rw [Int.cast_natCast, ZMod.natCast_eq_natCast_iff]
    exact ht₀p

end Arith

section SS

p2m_open "Polynomial WeierstrassCurve~card P2MW.S_WeierstrassCurve_exists_supersingular_endomorphism_natCard_ker_eq_odd_pow_stabilizing_cyclic.WeierstrassCurve Finset"

theorem Δ_legendreCurve {R : Type*} [CommRing R] (t : R) :
    (legendreCurve t).Δ = 16 * t ^ 2 * (t - 1) ^ 2 := by
  simp only [legendreCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

theorem twoTorsionPolynomial_legendreCurve {R : Type*} [CommRing R] (t : R) :
    (legendreCurve t).twoTorsionPolynomial.toPoly = C 4 * (X * ((X - 1) * (X - C t))) := by
  simp only [legendreCurve, WeierstrassCurve.twoTorsionPolynomial, Cubic.toPoly, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  have e1 : (0 ^ 2 + 4 * -(1 + t) : R) = -4 + (-4) * t := by ring
  have e2 : (2 * (2 * t + 0 * 0) : R) = 4 * t := by ring
  have e3 : (0 ^ 2 + 4 * 0 : R) = 0 := by ring
  rw [e1, e2, e3]
  simp only [map_neg, map_mul, map_add, map_ofNat, map_zero]
  ring

theorem hasseInvariant_legendreCurve' {R : Type*} [CommRing R] {q : ℕ} (hq : Odd q) (t : R) :
    (legendreCurve t).hasseInvariant q
      = (-4) ^ ((q - 1) / 2) * ((Polynomial.deuringPolynomial q).map (Int.castRingHom R)).eval t := by
  obtain ⟨m, rfl⟩ := hq
  have hm1 : (2 * m + 1 - 1) / 2 = m := by omega
  have hm2 : 2 * m + 1 - 1 = 2 * m := by omega
  rw [WeierstrassCurve.hasseInvariant, hm1, hm2, twoTorsionPolynomial_legendreCurve, mul_pow, mul_pow, ← C_pow,
    coeff_C_mul, coeff_X_pow_mul', if_pos (by omega), show 2 * m - m = m by omega, mul_pow, coeff_mul]

  have hX1 : ∀ i, ((X - 1 : R[X]) ^ m).coeff i = (-1) ^ (m - i) * (m.choose i : R) := fun i => by
    rw [show (X - 1 : R[X]) = X + C (-1) by rw [map_neg, map_one, sub_eq_add_neg], coeff_X_add_C_pow]
  have hXt : ∀ i, ((X - C t : R[X]) ^ m).coeff i = (-t) ^ (m - i) * (m.choose i : R) := fun i => by
    rw [show (X - C t : R[X]) = X + C (-t) by rw [map_neg, sub_eq_add_neg], coeff_X_add_C_pow]
  simp_rw [hX1, hXt]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

  rw [Polynomial.deuringPolynomial, hm1, Polynomial.map_sum, eval_finsetSum, mul_sum, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [mem_range] at hi
  simp only [Polynomial.map_mul, Polynomial.map_pow, map_X, eq_intCast, eval_mul, eval_pow, eval_X,
    Int.cast_pow, Int.cast_natCast, Polynomial.map_natCast, eval_natCast]
  rw [Nat.choose_symm (by omega : i ≤ m), show m - (m - i) = i by omega]
  have : ((-4 : R)) ^ m = 4 ^ m * ((-1) ^ (m - i) * (-1) ^ i) := by
    rw [← pow_add, show m - i + i = m by omega, ← mul_pow]; norm_num
  rw [this, neg_pow t]
  ring

theorem exists_supersingular (k : Type*) [Field k] [IsAlgClosed k] [DecidableEq k] (p : ℕ) [hp : Fact p.Prime]
    [CharP k p] :
    ∃ (E : WeierstrassCurve k) (_ : E.IsElliptic), ∀ P : E.toAffine.Point, p • P = 0 → P = 0 := by
  by_cases hp2 : p = 2
  · subst hp2
    have h0 := ModularCurve.zero_mem_ssJSet_of_lt_five (q := 2) (by norm_num) (K := k)
    exact ⟨WeierstrassCurve.ofJ 0, inferInstance, h0 (WeierstrassCurve.ofJ 0) (WeierstrassCurve.ofJ_j 0)⟩
  · have hpodd : Odd p := hp.out.odd_of_ne_two hp2
    have h2k : (2 : k) ≠ 0 := by
      intro h
      have := (CharP.cast_eq_zero_iff k p 2).mp (by exact_mod_cast h)
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
    set H : k[X] := (deuringPolynomial p).map (Int.castRingHom k) with hH
    have hdeg : H.degree ≠ 0 := by
      intro h0
      have h1 : H.natDegree = 0 := natDegree_eq_of_degree_eq_some (h0.trans (by rfl))
      rw [hH, natDegree_deuringPolynomial_map] at h1
      have := hp.out.two_le
      omega
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_root H hdeg
    have ht0 : t ≠ 0 := by
      rintro rfl
      have := eval_zero_deuringPolynomial_map (F := k) p
      rw [← hH, ht.eq_zero] at this
      exact zero_ne_one this
    have ht1 : t ≠ 1 := by
      rintro rfl
      have := eval_one_deuringPolynomial_map (F := k) p
      rw [← hH, ht.eq_zero] at this
      exact (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) this.symm
    haveI hE : (legendreCurve t).IsElliptic := by
      refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
      rw [Δ_legendreCurve]
      refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ ht0)) (pow_ne_zero _ (sub_ne_zero.mpr ht1))
      have : (16 : k) = 2 ^ 4 := by norm_num
      rw [this]; exact pow_ne_zero _ h2k
    refine ⟨legendreCurve t, hE, ?_⟩
    rw [forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero p hp2, hasseInvariant_legendreCurve' hpodd, ← hH,
      ht.eq_zero, mul_zero]

end SS

section OverAlgebraic

p2m_open "WeierstrassCurve~card P2MW.S_WeierstrassCurve_exists_supersingular_endomorphism_natCard_ker_eq_odd_pow_stabilizing_cyclic.WeierstrassCurve QuaternionAlgebra"

variable {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]

theorem mem_rationalHomSet_of_mem_rationalEndSubring (W : WeierstrassCurve k) [W.IsElliptic]
    {x : AddMonoid.End (W.baseChange k).toAffine.Point} (hx : x ∈ rationalEndSubring k W) :
    (x : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point) ∈ rationalHomSet k W W := by
  induction hx using Subring.closure_induction with
  | mem y hy => exact hy
  | zero => exact zero_mem_rationalHomSet k W W
  | one => exact id_mem_rationalHomSet k W
  | add y z _ _ hy hz => exact add_mem_rationalHomSet k W W hy hz
  | neg y _ hy => exact neg_mem_rationalHomSet k W W hy
  | mul y z _ _ hy hz => exact comp_mem_rationalHomSet k W W W hz hy

theorem div_step (p : ℕ) [Fact p.Prime] [CharP k p] (E : WeierstrassCurve k) [E.IsElliptic]
    (hss : ∀ P : E.toAffine.Point, p • P = 0 → P = 0) (t q : ℤ) (N : ℕ)
    {γ : E.toAffine.Point →+ E.toAffine.Point} (hγ : γ ∈ rationalHomSet k E E)
    (hchar : γ.comp γ + (((p * N : ℕ) : ℤ) ^ 2 * q) • AddMonoidHom.id _ = (((p * N : ℕ) : ℤ) * t) • γ) :
    ∃ γ' : E.toAffine.Point →+ E.toAffine.Point, γ' ∈ rationalHomSet k E E ∧
      γ'.comp γ' + ((N : ℤ) ^ 2 * q) • AddMonoidHom.id _ = ((N : ℤ) * t) • γ' := by
  obtain ⟨γ', hγ', hγγ'⟩ : ∃ γ' : E.toAffine.Point →+ E.toAffine.Point, γ' ∈ rationalHomSet k E E ∧
      γ - (0 : ℤ) • AddMonoidHom.id _ = (p : ℤ) • γ' :=
    exists_mem_rationalHomSet_sub_smul_id_eq_char_smul_of_dvd_of_sq_dvd p E hγ _ _ hchar 0
      ⟨(N : ℤ) * t, by push_cast; ring⟩ ⟨(N : ℤ) ^ 2 * q, by push_cast; ring⟩
  have hpt : ∀ P : E.toAffine.Point, γ P = (p : ℤ) • γ' P := fun P => by
    have := congrArg (fun f : E.toAffine.Point →+ E.toAffine.Point => f P) hγγ'
    simpa using this
  refine ⟨γ', hγ', ?_⟩
  have hss' : ∀ Y : E.toAffine.Point, (p : ℤ) • Y = 0 → Y = 0 := fun Y hY =>
    hss Y (by rw [← natCast_zsmul]; exact hY)
  ext P
  have hP := congrArg (fun f : E.toAffine.Point →+ E.toAffine.Point => f P) hchar
  simp only [AddMonoidHom.add_apply, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.smul_apply,
    AddMonoidHom.id_apply] at hP ⊢
  rw [hpt P, map_zsmul, hpt (γ' P), smul_smul] at hP
  have hP' : ((p : ℤ) * p) • (γ' (γ' P) + ((N : ℤ) ^ 2 * q) • P - ((N : ℤ) * t) • γ' P) = 0 := by
    rw [← sub_eq_zero.mpr hP]
    push_cast
    module
  rw [← sub_eq_zero]
  apply hss'
  apply hss'
  rw [smul_smul]
  exact hP'

theorem exists_over_algebraic (k : Type*) [Field k] [IsAlgClosed k] [DecidableEq k] (p : ℕ) [Fact p.Prime]
    [CharP k p] [Algebra (ZMod p) k] [Algebra.IsAlgebraic (ZMod p) k]
    (M : ℕ) (hM : M ≠ 0) (hpM : ¬ p ∣ M) (t₁ n₂ : ℤ) (ht₁M : IsCoprime t₁ M)
    (hΔ : t₁ ^ 2 < 4 * (M * n₂)) (hsq : ¬ IsSquare ((t₁ ^ 2 - 4 * (M * n₂) : ℤ) : ℚ_[p])) :
    ∃ (W : WeierstrassCurve k) (_ : W.IsElliptic) (C : AddSubgroup W.toAffine.Point)
      (α₁ : W.toAffine.Point →+ W.toAffine.Point),
      (∀ P : W.toAffine.Point, p • P = 0 → P = 0) ∧ IsAddCyclic C ∧ Nat.card C = M ∧ (∀ T ∈ C, α₁ T ∈ C) ∧
      α₁ ∈ rationalHomSet k W W ∧ α₁.comp α₁ + (M * n₂) • AddMonoidHom.id _ = t₁ • α₁ := by
  have hp := (Fact.out : p.Prime)
  set n₁ : ℤ := M * n₂ with hn₁

  obtain ⟨E₀, hE₀, hss⟩ := exists_supersingular k p
  obtain ⟨a, b, hdef, Λ, hΛ, θ, hθ, hθΛ⟩ :=
    exists_isDefiniteRamifiedExactlyAt_isMaximalOrder_range_eq_rationalEndSubring (k := k) p E₀ hss

  obtain ⟨β, hβ⟩ := QuaternionAlgebra.exists_isQuadraticDatum_of_sq_lt_four_mul_of_not_isSquare_padic p hdef t₁ n₁ hΔ hsq
  obtain ⟨N₀, hN₀, hN₀β⟩ := exists_natCast_smul_mem_of_mem_span (Λ := Λ) (y := β) (by rw [hΛ.isOrder.spanTop]; trivial)
  obtain ⟨γ₀, hγ₀⟩ : ∃ γ₀ : rationalEndSubring k E₀, θ γ₀ = ((N₀ : ℕ) : ℤ) • β := by
    have : ((N₀ : ℕ) : ℤ) • β ∈ Set.range θ := by rw [hθΛ]; exact hN₀β
    exact this

  have hrel₀ : γ₀ * γ₀ - ((N₀ : ℤ) * t₁) • γ₀ + ((N₀ : ℤ) ^ 2 * n₁) • (1 : rationalEndSubring k E₀) = 0 := by
    apply hθ
    rw [map_zero, map_add, map_sub, map_mul, map_zsmul, map_zsmul, map_one, hγ₀]
    rw [isQuadraticDatum_iff] at hβ
    have e1 : (((N₀ : ℕ) : ℤ) • β) * (((N₀ : ℕ) : ℤ) • β) = ((N₀ : ℚ) ^ 2) • (β * β) := by
      rw [smul_mul_smul_comm, ← Int.cast_smul_eq_zsmul ℚ]; push_cast; ring_nf
    have e2 : ((N₀ : ℤ) * t₁) • (((N₀ : ℕ) : ℤ) • β) = ((N₀ : ℚ) ^ 2) • ((t₁ : ℚ) • β) := by
      rw [smul_smul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]; push_cast; ring_nf
    have e3 : ((N₀ : ℤ) ^ 2 * n₁) • (1 : ℍ[ℚ, a, b]) = ((N₀ : ℚ) ^ 2) • ((n₁ : ℚ) • (1 : ℍ[ℚ, a, b])) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul]; push_cast; ring_nf
    rw [e1, e2, e3, ← smul_sub, ← smul_add, hβ, smul_zero]

  set γ : E₀.toAffine.Point →+ E₀.toAffine.Point := (γ₀ : AddMonoid.End (E₀.baseChange k).toAffine.Point) with hγdef
  have hγ : γ ∈ rationalHomSet k E₀ E₀ := mem_rationalHomSet_of_mem_rationalEndSubring E₀ γ₀.2
  have hcharγ : γ.comp γ + ((N₀ : ℤ) ^ 2 * n₁) • AddMonoidHom.id _ = ((N₀ : ℤ) * t₁) • γ := by
    have hval := congrArg (rationalEndSubring k E₀).subtype hrel₀
    rw [map_zero, map_add, map_sub, map_mul, map_zsmul, map_zsmul, map_one, Subring.subtype_apply] at hval
    have hval' : γ.comp γ - ((N₀ : ℤ) * t₁) • γ + ((N₀ : ℤ) ^ 2 * n₁) • AddMonoidHom.id _ = 0 := hval
    rw [← sub_eq_zero, ← hval']
    abel

  have hloop : ∀ (j N : ℕ) (δ : E₀.toAffine.Point →+ E₀.toAffine.Point), δ ∈ rationalHomSet k E₀ E₀ →
      δ.comp δ + (((p ^ j * N : ℕ) : ℤ) ^ 2 * n₁) • AddMonoidHom.id _ = (((p ^ j * N : ℕ) : ℤ) * t₁) • δ →
      ∃ δ' : E₀.toAffine.Point →+ E₀.toAffine.Point, δ' ∈ rationalHomSet k E₀ E₀ ∧
        δ'.comp δ' + ((N : ℤ) ^ 2 * n₁) • AddMonoidHom.id _ = ((N : ℤ) * t₁) • δ' := by
    intro j
    induction j with
    | zero =>
      intro N δ hδ h
      refine ⟨δ, hδ, ?_⟩
      simpa only [pow_zero, one_mul] using h
    | succ j ih =>
      intro N δ hδ h
      have h' : δ.comp δ + (((p * (p ^ j * N) : ℕ) : ℤ) ^ 2 * n₁) • AddMonoidHom.id _ =
          (((p * (p ^ j * N) : ℕ) : ℤ) * t₁) • δ := by
        rw [show p * (p ^ j * N) = p ^ (j + 1) * N by ring]; exact h
      obtain ⟨δ₁, hδ₁, h₁⟩ := div_step p E₀ hss t₁ n₁ (p ^ j * N) hδ h'
      exact ih N δ₁ hδ₁ h₁
  set N : ℕ := N₀ / p ^ N₀.factorization p with hNdef
  have hN₀eq : p ^ N₀.factorization p * N = N₀ := Nat.ordProj_mul_ordCompl_eq_self N₀ p
  have hpN : ¬ p ∣ N := Nat.not_dvd_ordCompl hp hN₀
  have hNk : (N : k) ≠ 0 := fun h => hpN ((CharP.cast_eq_zero_iff k p N).mp h)
  obtain ⟨γ₁, hγ₁, hcharγ₁⟩ := hloop (N₀.factorization p) N γ hγ (by rw [hN₀eq]; exact hcharγ)

  obtain ⟨W, hW, χ, α₁, hχ, hsurj, hkercard, hα₁, hrelα, -⟩ :=
    exists_mem_rationalHomSet_comp_self_add_smul_eq_smul_of_natCast_mul E₀ hγ₁ N hNk t₁ n₁ hcharγ₁
  haveI := hW

  have hssW : ∀ P : W.toAffine.Point, p • P = 0 → P = 0 := by
    intro P hP
    obtain ⟨Q, rfl⟩ := hsurj P
    set c := Nat.card χ.ker with hc
    have hc0 : c ≠ 0 := fun h => hkercard (by rw [h, Nat.cast_zero])
    haveI : Finite χ.ker := Nat.finite_of_card_ne_zero hc0
    have hpQ : p • Q ∈ χ.ker := by rw [AddMonoidHom.mem_ker, map_nsmul, hP]
    have hcpQ : c • (p • Q) = 0 := by
      have h := card_nsmul_eq_zero' (G := χ.ker) (x := ⟨p • Q, hpQ⟩)
      have := congrArg Subtype.val h
      first | simpa using this | (simp at this; exact this) | exact this
    have hcQ : c • Q = 0 := hss (c • Q) (by rw [smul_comm]; exact hcpQ)
    have hcop : IsCoprime (c : ℤ) (p : ℤ) := by
      rw [Nat.isCoprime_iff_coprime, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      exact hkercard ((CharP.cast_eq_zero_iff k p c).mpr h)
    obtain ⟨u, v, huv⟩ := hcop
    calc χ Q = (1 : ℤ) • χ Q := (one_smul _ _).symm
      _ = u • ((c : ℤ) • χ Q) + v • ((p : ℤ) • χ Q) := by rw [← huv, add_smul, mul_smul, mul_smul]
      _ = 0 := by
        rw [natCast_zsmul, natCast_zsmul, ← map_nsmul, hcQ, map_zero, hP, smul_zero, smul_zero, add_zero]

  have hMk : (M : k) ≠ 0 := fun h => hpM ((CharP.cast_eq_zero_iff k p M).mp h)
  obtain ⟨e⟩ := nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (F := k) (K := k) W (n := M) hMk
  obtain ⟨v, w, hvw⟩ := ht₁M
  have huv : (M : ℤ) ∣ t₁ * v - 1 := ⟨-w, by linear_combination hvw⟩
  have hf : ∀ x : W.toAffine.Point, (M : ℤ) • x = 0 → α₁ (α₁ x) = t₁ • α₁ x := by
    intro x hx
    have := congrArg (fun f : W.toAffine.Point →+ W.toAffine.Point => f x) hrelα
    simp only [AddMonoidHom.add_apply, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.smul_apply,
      AddMonoidHom.id_apply] at this
    rw [← this, hn₁, mul_comm, mul_smul, hx, smul_zero, add_zero]
  obtain ⟨C, hCcyc, hCcard, hCstab⟩ :=
    AddMonoidHom.exists_isAddCyclic_natCard_eq_forall_apply_mem_of_apply_apply_eq_smul hM e α₁ t₁ v huv hf
  exact ⟨W, hW, C, α₁, hssW, hCcyc, hCcard, hCstab, hα₁, hrelα⟩

end OverAlgebraic

section Assembly

p2m_open "WeierstrassCurve~card P2MW.S_WeierstrassCurve_exists_supersingular_endomorphism_natCard_ker_eq_odd_pow_stabilizing_cyclic.WeierstrassCurve"

section

variable {F : Type*} [Field F] (K : Type*) [Field K] [Algebra F K] [IsAlgClosed K] [DecidableEq K]

theorem zsmul_mem_rationalHomSet (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic]
    {α : (W₁.baseChange K).toAffine.Point →+ (W₂.baseChange K).toAffine.Point}
    (hα : α ∈ rationalHomSet K W₁ W₂) (z : ℤ) : z • α ∈ rationalHomSet K W₁ W₂ := by
  induction z using Int.induction_on with
  | zero => rw [zero_zsmul]; exact zero_mem_rationalHomSet K W₁ W₂
  | succ n ih => rw [add_zsmul, one_zsmul]; exact add_mem_rationalHomSet K W₁ W₂ ih hα
  | pred n ih =>
    rw [sub_zsmul, one_zsmul]
    exact add_mem_rationalHomSet K W₁ W₂ ih (neg_mem_rationalHomSet K W₁ W₂ hα)

end

theorem mem_rationalHomSet_baseChange {k₀ : Type*} [Field k₀] (K : Type*) [Field K] [Algebra k₀ K] [DecidableEq K]
    (W₁ W₂ : WeierstrassCurve k₀)
    {α : (W₁.baseChange K).toAffine.Point →+ (W₂.baseChange K).toAffine.Point}
    (hα : α ∈ rationalHomSet K W₁ W₂) :
    (α : ((W₁.baseChange K).baseChange K).toAffine.Point →+ ((W₂.baseChange K).baseChange K).toAffine.Point) ∈
      rationalHomSet K (W₁.baseChange K) (W₂.baseChange K) := by
  rcases hα with hα | ⟨nX, dX, nY, dY, B, hB, h⟩
  · exact Or.inl hα
  · refine Or.inr ⟨nX.map (Polynomial.mapRingHom (algebraMap k₀ K)), dX.map (Polynomial.mapRingHom (algebraMap k₀ K)),
      nY.map (Polynomial.mapRingHom (algebraMap k₀ K)), dY.map (Polynomial.mapRingHom (algebraMap k₀ K)), B, hB,
      fun x y hxy hxB => ?_⟩
    have key : ∀ q : Polynomial (Polynomial k₀),
        evalEvalBC K (F := K) (q.map (Polynomial.mapRingHom (algebraMap k₀ K))) x y = evalEvalBC K (F := k₀) q x y := by
      intro q
      simp only [evalEvalBC, Polynomial.map_map, Algebra.algebraMap_self, Polynomial.mapRingHom_id]
      congr 1
    obtain ⟨h1, h2, h', h3⟩ := h x y hxy hxB
    refine ⟨by rw [key]; exact h1, by rw [key]; exact h2, ?_⟩
    simp only [key]
    exact ⟨h', h3⟩

theorem eq_zero_of_forall_prime_torsion {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (E : WeierstrassCurve K) [E.IsElliptic] {β : E.toAffine.Point →+ E.toAffine.Point}
    (hβ : β ∈ rationalHomSet K E E) (b : ℕ)
    (h : ∀ ℓ : ℕ, ℓ.Prime → b < ℓ → ∀ P : E.toAffine.Point, (ℓ : ℤ) • P = 0 → β P = 0) : β = 0 := by
  by_contra hβ0
  obtain ⟨σ, -, d, hd, hdual⟩ :
      ∃ σ : E.toAffine.Point →+ E.toAffine.Point, σ ∈ rationalHomSet K E E ∧ ∃ n : ℤ, 0 < n ∧
        AddMonoidHom.IsDualPair β σ n :=
    exists_isDualPair_of_mem_rationalHomSet (F := K) K E E hβ hβ0
  obtain ⟨ℓ, hℓb, hℓ⟩ := Nat.exists_infinite_primes (b + d.toNat + ringChar K + 1)
  have hℓchar : (ℓ : K) ≠ 0 := by
    intro h0
    have hdvd := (ringChar.spec K ℓ).mp h0
    rcases (Nat.dvd_prime hℓ).mp hdvd with hc | hc
    · exact CharP.ringChar_ne_one hc
    · omega

  have hcard := card_torsion_of_isAlgClosed (F := K) (K := K) E (n := ℓ) hℓchar
  haveI : Finite (Submodule.torsionBy ℤ (E.baseChange K).toAffine.Point (ℓ : ℤ)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hℓ.ne_zero)
  have hnt : Nontrivial (Submodule.torsionBy ℤ (E.baseChange K).toAffine.Point (ℓ : ℤ)) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    exact Nat.one_lt_pow two_ne_zero hℓ.one_lt
  obtain ⟨⟨P, hP⟩, hP0⟩ := exists_ne (0 : Submodule.torsionBy ℤ (E.baseChange K).toAffine.Point (ℓ : ℤ))
  have hPℓ : (ℓ : ℤ) • P = 0 := (Submodule.mem_torsionBy_iff _ _).mp hP
  have hP0' : (P : E.toAffine.Point) ≠ 0 := fun h0 => hP0 (Subtype.ext h0)
  have hβP : β P = 0 := h ℓ hℓ (by omega) P hPℓ
  have hdP : d • P = 0 := by
    have h1 : σ (β P) = d • P := hdual.comp_left P
    rw [hβP, map_zero] at h1
    exact h1.symm

  have hcop : IsCoprime d (ℓ : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h1 : Int.gcd d ℓ ∣ ℓ := Int.gcd_dvd_natAbs_right d ℓ |>.trans (by simp)
    rcases (Nat.dvd_prime hℓ).mp h1 with h1 | h1
    · exact h1
    · exfalso
      have h2 : ((Int.gcd d ℓ : ℕ) : ℤ) ∣ d := Int.gcd_dvd_left d ℓ
      rw [h1] at h2
      have := Int.le_of_dvd hd h2
      omega
  obtain ⟨u, v, huv⟩ := hcop
  apply hP0'
  calc (P : E.toAffine.Point) = (1 : ℤ) • P := (one_smul _ _).symm
    _ = u • (d • P) + v • ((ℓ : ℤ) • P) := by rw [← huv, add_smul, mul_smul, mul_smul]
    _ = 0 := by rw [hdP, hPℓ, smul_zero, smul_zero, add_zero]

theorem exists_map_eq_of_torsion {k₀ : Type*} (K : Type*) [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀]
    [IsAlgClosed K] [DecidableEq k₀] [DecidableEq K] (W : WeierstrassCurve k₀) [W.IsElliptic] {ℓ : ℕ}
    (hℓ0 : (ℓ : k₀) ≠ 0) (hℓK : (ℓ : K) ≠ 0) (Q : (W.baseChange K).toAffine.Point) (hQ : (ℓ : ℤ) • Q = 0) :
    ∃ P : (W.baseChange k₀).toAffine.Point,
      WeierstrassCurve.Affine.Point.map (IsScalarTower.toAlgHom k₀ k₀ K) P = Q := by
  set π := WeierstrassCurve.Affine.Point.map (W' := W) (IsScalarTower.toAlgHom k₀ k₀ K) with hπ
  have hπinj : Function.Injective π := WeierstrassCurve.Affine.Point.map_injective _
  set T₀ := Submodule.torsionBy ℤ (W.baseChange k₀).toAffine.Point (ℓ : ℤ) with hT₀
  set T := Submodule.torsionBy ℤ (W.baseChange K).toAffine.Point (ℓ : ℤ) with hT
  have hcard₀ : Nat.card T₀ = ℓ ^ 2 := card_torsion_of_isAlgClosed (F := k₀) (K := k₀) W hℓ0
  have hcard : Nat.card T = ℓ ^ 2 := card_torsion_of_isAlgClosed (F := k₀) (K := K) W hℓK
  let f : T₀ → T := fun x => ⟨π x, by
    rw [hT, Submodule.mem_torsionBy_iff]
    change (ℓ : ℤ) • π x = 0
    rw [← map_zsmul, (Submodule.mem_torsionBy_iff _ _).mp x.2, map_zero]⟩
  have hfinj : Function.Injective f := fun x y hxy => Subtype.ext (hπinj (congrArg Subtype.val hxy))
  haveI : Finite T := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact pow_ne_zero _ (fun h => hℓK (by rw [h, Nat.cast_zero])))
  have hbij : Function.Bijective f := hfinj.bijective_of_nat_card_le (by rw [hcard, hcard₀])
  obtain ⟨x, hx⟩ := hbij.2 ⟨Q, (Submodule.mem_torsionBy_iff _ _).mpr hQ⟩
  exact ⟨x, congrArg Subtype.val hx⟩

theorem final
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (M s : ℕ) [NeZero M] (hs : s.Prime) (hsp : s ≠ p) (hpM : ¬ p ∣ M) (hsM : ¬ s ∣ M) :
    ∃ (E : WeierstrassCurve K) (_ : E.IsElliptic) (C : AddSubgroup E.toAffine.Point)
      (α α' : (E.baseChange K).toAffine.Point →+ (E.baseChange K).toAffine.Point) (n : ℕ),
      (∀ P : E.toAffine.Point, p • P = 0 → P = 0) ∧
      IsAddCyclic C ∧ Nat.card C = M ∧ (∀ T ∈ C, α T ∈ C) ∧
      α ∈ WeierstrassCurve.rationalHomSet K E E ∧ α' ∈ WeierstrassCurve.rationalHomSet K E E ∧
      α'.comp α = s ^ n • AddMonoidHom.id _ ∧ α.comp α' = s ^ n • AddMonoidHom.id _ ∧
      Odd n ∧ Nat.card α.ker = s ^ n := by
  have hp := (Fact.out : p.Prime)
  have hM0 : M ≠ 0 := NeZero.ne M

  obtain ⟨n, m, t₁, n₂, hodd, hm0, hnorm, hcop, hlt, hsdvd, hnsq⟩ := exists_params p s M hs hsp hM0 hpM hsM
  set t : ℤ := 2 + m * t₁ with ht
  set n₁ : ℤ := M * n₂ with hn₁
  have hΔ : t ^ 2 - 4 * (s : ℤ) ^ n = (m : ℤ) ^ 2 * (t₁ ^ 2 - 4 * n₁) := by rw [← hnorm, ht]; ring
  have hlt1 : t₁ ^ 2 < 4 * n₁ := by
    have h1 : (m : ℤ) ^ 2 * (t₁ ^ 2 - 4 * n₁) < 0 := by rw [← hΔ]; linarith
    have h2 : (0 : ℤ) < (m : ℤ) ^ 2 := by positivity
    nlinarith
  have hnsq1 : ¬ IsSquare ((t₁ ^ 2 - 4 * n₁ : ℤ) : ℚ_[p]) := by
    rintro ⟨y, hy⟩
    apply hnsq
    refine ⟨(m : ℚ_[p]) * y, ?_⟩
    have e1 : ((t ^ 2 - 4 * (s : ℤ) ^ n : ℤ) : ℚ_[p]) = (m : ℚ_[p]) ^ 2 * ((t₁ ^ 2 - 4 * n₁ : ℤ) : ℚ_[p]) := by
      rw [hΔ]; push_cast; ring
    rw [e1, hy]; ring

  let k₀ := AlgebraicClosure (ZMod p)
  letI : DecidableEq k₀ := Classical.decEq _
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  let ι : k₀ →ₐ[ZMod p] K := IsAlgClosed.lift
  letI : Algebra k₀ K := ι.toRingHom.toAlgebra
  obtain ⟨W, hW, C₁, α₁, hssW, hC₁cyc, hC₁card, hC₁stab, hα₁, hrel₁⟩ :=
    exists_over_algebraic k₀ p M hM0 hpM t₁ n₂ hcop hlt1 hnsq1
  haveI := hW

  set E : WeierstrassCurve K := W.baseChange K with hE
  haveI hEell : E.IsElliptic := by rw [hE, WeierstrassCurve.baseChange]; infer_instance
  set π : W.toAffine.Point →+ E.toAffine.Point :=
    WeierstrassCurve.Affine.Point.map (W' := W) (IsScalarTower.toAlgHom k₀ k₀ K) with hπ
  have hπinj : Function.Injective π := WeierstrassCurve.Affine.Point.map_injective _
  obtain ⟨α₁K, hα₁K, hext⟩ :
      ∃ α₁K : E.toAffine.Point →+ E.toAffine.Point, α₁K ∈ rationalHomSet K W W ∧
        ∀ P : W.toAffine.Point, α₁K (π P) = π (α₁ P) :=
    exists_mem_rationalHomSet_apply_map_eq_map_apply (F := k₀) k₀ K W W hα₁
  have hα₁K' : α₁K ∈ rationalHomSet K E E := mem_rationalHomSet_baseChange K W W hα₁K

  have hrelK : α₁K.comp α₁K + n₁ • AddMonoidHom.id _ = t₁ • α₁K := by
    set βK : E.toAffine.Point →+ E.toAffine.Point :=
      α₁K.comp α₁K + n₁ • AddMonoidHom.id _ + (-t₁) • α₁K with hβK
    have hβKmem : βK ∈ rationalHomSet K E E :=
      add_mem_rationalHomSet K E E (add_mem_rationalHomSet K E E (comp_mem_rationalHomSet K E E E hα₁K' hα₁K')
        (zsmul_mem_rationalHomSet K E E (id_mem_rationalHomSet K E) n₁)) (zsmul_mem_rationalHomSet K E E hα₁K' (-t₁))
    have hβKπ : ∀ P : W.toAffine.Point, βK (π P) = 0 := by
      intro P
      have h1 := congrArg (fun f : W.toAffine.Point →+ W.toAffine.Point => f P) hrel₁
      simp only [AddMonoidHom.add_apply, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.smul_apply,
        AddMonoidHom.id_apply] at h1
      rw [← hn₁] at h1
      simp only [hβK, AddMonoidHom.add_apply, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.smul_apply,
        AddMonoidHom.id_apply, hext, neg_smul, AddMonoidHom.neg_apply]
      rw [← map_zsmul π, ← map_zsmul π, ← map_neg π, ← map_add π, ← map_add π]
      have h2 : α₁ (α₁ P) + n₁ • P + -(t₁ • α₁ P) = 0 := by rw [h1, add_neg_cancel]
      exact (congrArg π h2).trans (map_zero π)
    have hℓ0 : ∀ ℓ : ℕ, ℓ.Prime → p < ℓ → (ℓ : k₀) ≠ 0 := fun ℓ hℓ hpℓ h0 =>
      absurd ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp ((CharP.cast_eq_zero_iff k₀ p ℓ).mp h0)) (by omega)
    have hℓK : ∀ ℓ : ℕ, ℓ.Prime → p < ℓ → (ℓ : K) ≠ 0 := fun ℓ hℓ hpℓ h0 =>
      absurd ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp ((CharP.cast_eq_zero_iff K p ℓ).mp h0)) (by omega)
    have hzero := eq_zero_of_forall_prime_torsion E hβKmem p (fun ℓ hℓ hpℓ Q hQ => by
      obtain ⟨P, rfl⟩ := exists_map_eq_of_torsion K W (hℓ0 ℓ hℓ hpℓ) (hℓK ℓ hℓ hpℓ) Q hQ
      exact hβKπ P)
    rw [hβK, neg_smul, add_neg_eq_zero] at hzero
    exact hzero

  set αK : E.toAffine.Point →+ E.toAffine.Point := AddMonoidHom.id _ + (m : ℤ) • α₁K with hαK
  set α'K : E.toAffine.Point →+ E.toAffine.Point := t • AddMonoidHom.id _ + (-1 : ℤ) • αK with hα'K
  have hαKmem : αK ∈ rationalHomSet K E E :=
    add_mem_rationalHomSet K E E (id_mem_rationalHomSet K E) (zsmul_mem_rationalHomSet K E E hα₁K' m)
  have hα'Kmem : α'K ∈ rationalHomSet K E E :=
    add_mem_rationalHomSet K E E (zsmul_mem_rationalHomSet K E E (id_mem_rationalHomSet K E) t)
      (zsmul_mem_rationalHomSet K E E hαKmem (-1))
  have hrelKP : ∀ P : E.toAffine.Point, α₁K (α₁K P) = t₁ • α₁K P - n₁ • P := fun P => by
    have := congrArg (fun f : E.toAffine.Point →+ E.toAffine.Point => f P) hrelK
    simp only [AddMonoidHom.add_apply, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.smul_apply,
      AddMonoidHom.id_apply] at this
    rw [← this, add_sub_cancel_right]
  have hsn : ((s ^ n : ℕ) : ℤ) = 1 + m * t₁ + (m : ℤ) ^ 2 * n₁ := by push_cast; rw [hnorm]
  have hcharα : αK.comp αK + ((s ^ n : ℕ) : ℤ) • AddMonoidHom.id _ = t • αK := by
    ext P
    simp only [hαK, AddMonoidHom.add_apply, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.smul_apply,
      AddMonoidHom.id_apply, map_add, map_zsmul, hrelKP, hsn, ht]
    module
  have hcharαP : ∀ P : E.toAffine.Point, αK (αK P) = t • αK P - ((s ^ n : ℕ) : ℤ) • P := fun P => by
    have := congrArg (fun f : E.toAffine.Point →+ E.toAffine.Point => f P) hcharα
    simp only [AddMonoidHom.add_apply, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.smul_apply,
      AddMonoidHom.id_apply] at this
    rw [← this, add_sub_cancel_right]
  have hdual1 : α'K.comp αK = s ^ n • AddMonoidHom.id _ := by
    ext P
    simp only [hα'K, AddMonoidHom.add_apply, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.smul_apply,
      AddMonoidHom.id_apply, hcharαP, neg_smul, one_smul, AddMonoidHom.neg_apply]
    rw [← natCast_zsmul]
    abel
  have hdual2 : αK.comp α'K = s ^ n • AddMonoidHom.id _ := by
    ext P
    simp only [hα'K, AddMonoidHom.add_apply, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.smul_apply,
      AddMonoidHom.id_apply, map_add, map_zsmul, map_neg, hcharαP, neg_smul, one_smul, AddMonoidHom.neg_apply]
    rw [← natCast_zsmul]
    abel

  have hsK : (s : K) ≠ 0 := fun h0 => hsp ((Nat.prime_dvd_prime_iff_eq hp hs).mp ((CharP.cast_eq_zero_iff K p s).mp h0)).symm
  have hker : Nat.card αK.ker = s ^ n := by
    refine (isAddCyclic_ker_and_card_ker_eq_of_comp_self_add_smul_eq_smul E hαKmem t (s ^ n) hcharα
      (by push_cast; exact pow_ne_zero _ hsK) ?_ ?_).2
    · intro x hx
      nlinarith [sq_nonneg (2 * x - t), hlt, hx]
    · intro ℓ hℓ hℓt hℓ2
      have h1 : (ℓ : ℤ) ∣ (s : ℤ) ^ n := (dvd_pow_self (ℓ : ℤ) two_ne_zero).trans (by push_cast at hℓ2; exact hℓ2)
      have h2 : ℓ ∣ s ^ n := by exact_mod_cast h1
      have h3 : ℓ = s := (Nat.prime_dvd_prime_iff_eq hℓ hs).mp (hℓ.dvd_of_dvd_pow h2)
      subst h3
      exact hsdvd hℓt

  have hssE : ∀ P : E.toAffine.Point, p • P = 0 → P = 0 := by
    have hj := j_mem_ssJSet_of_forall_smul_eq_zero (κ := k₀) p W hssW
    have hjK := ModularCurve.mem_ssJSet_map_of_isAlgClosed (q := p) (algebraMap k₀ K) W.j hj
    exact hjK E (W.map_j (algebraMap k₀ K))

  set C : AddSubgroup E.toAffine.Point := C₁.map π with hC
  have hCcyc : IsAddCyclic C := by
    haveI := hC₁cyc
    rw [hC]
    exact isAddCyclic_of_surjective _ (AddMonoidHom.addSubgroupMap_surjective π C₁)
  have hCcard : Nat.card C = M := by
    rw [hC, AddSubgroup.card_map_of_injective hπinj]
    exact hC₁card
  have hCstab : ∀ T ∈ C, αK T ∈ C := by
    intro T hT
    rw [hC, AddSubgroup.mem_map] at hT
    obtain ⟨T₀, hT₀, rfl⟩ := hT
    rw [hC, AddSubgroup.mem_map]
    refine ⟨T₀ + m • α₁ T₀, C₁.add_mem hT₀ (C₁.nsmul_mem (hC₁stab T₀ hT₀) m), ?_⟩
    simp only [hαK, AddMonoidHom.add_apply, AddMonoidHom.smul_apply, AddMonoidHom.id_apply, map_add, map_nsmul,
      hext, natCast_zsmul]
  exact ⟨E, inferInstance, C, αK, α'K, n, hssE, hCcyc, hCcard, hCstab, hαKmem, hα'Kmem, hdual1, hdual2, hodd, hker⟩

end Assembly

end WeierstrassCurve.OddPowSupersingularPort

open WeierstrassCurve.OddPowSupersingularPort in
theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (M s : ℕ) [NeZero M] (hs : s.Prime) (hsp : s ≠ p) (hpM : ¬ p ∣ M) (hsM : ¬ s ∣ M) :
    ∃ (E : WeierstrassCurve K) (_ : E.IsElliptic) (C : AddSubgroup E.toAffine.Point)
      (α α' : (E.baseChange K).toAffine.Point →+ (E.baseChange K).toAffine.Point) (n : ℕ),
      (∀ P : E.toAffine.Point, p • P = 0 → P = 0) ∧
      IsAddCyclic C ∧ Nat.card C = M ∧ (∀ T ∈ C, α T ∈ C) ∧
      α ∈ WeierstrassCurve.rationalHomSet K E E ∧ α' ∈ WeierstrassCurve.rationalHomSet K E E ∧
      α'.comp α = s ^ n • AddMonoidHom.id _ ∧ α.comp α' = s ^ n • AddMonoidHom.id _ ∧
      Odd n ∧ Nat.card α.ker = s ^ n :=
  final K p M s hs hsp hpM hsM

end S_WeierstrassCurve_exists_supersingular_endomorphism_natCard_ker_eq_odd_pow_stabilizing_cyclic
end P2MW
export P2MW.S_WeierstrassCurve_exists_supersingular_endomorphism_natCard_ker_eq_odd_pow_stabilizing_cyclic (solution)
