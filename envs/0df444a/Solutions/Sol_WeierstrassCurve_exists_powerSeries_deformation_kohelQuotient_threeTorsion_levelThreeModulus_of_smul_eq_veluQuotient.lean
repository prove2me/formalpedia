-- Prove2me | solution 1 for WeierstrassCurve.exists_powerSeries_deformation_kohelQuotient_threeTorsion_levelThreeModulus_of_smul_eq_veluQuotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/1026308f-1581-549e-9e50-3505b69c7f77

import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_WeierstrassCurve_KernelPolynomial
import Definitions.Def_WeierstrassCurve_KohelQuotient
import Definitions.Def_WeierstrassCurve_LevelThreeModulus
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_map_levelThreeModulus_kohelQuotient_sub_ne_zero_of_map_j_ne_C
import Theorems.Thm_WeierstrassCurve_exists_equation_and_eval_Psi3_eq_zero_and_map_eq_of_isAdicComplete
import Theorems.Thm_WeierstrassCurve_exists_powerSeries_isElliptic_variableChange_smul_map_eq_and_map_j_ne_C
import Theorems.Thm_Polynomial_exists_monic_mul_eq_and_map_eq_of_isCoprime_of_isAdicComplete
import Theorems.Thm_WeierstrassCurve_kohelQuotient_kernelPolynomial_eq_veluQuotient
import Theorems.Thm_WeierstrassCurve_separable_prePsi_of_isUnit
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_powerSeries_deformation_kohelQuotient_threeTorsion_levelThreeModulus_of_smul_eq_veluQuotient
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false

open Polynomial IsLocalRing

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.Y_eq_of_Y_ne variableChange_j VariableChange.ext a₃ map_map preΨ'_ne_zero map Ψ₃ Affine.Point.some leadingCoeff_preΨ' map_preΨ' VariableChange.map_u preΨ' toAffine Affine.Point map_Δ Affine.Point.some_ne_zero Δ VariableChange preΨ'_three Affine.Point.neg_some map_variableChange j veluQuotient oddOrderSummingSet mem_oddOrderSummingSet kernelPolynomial kernelPolynomial_eq_multiset_prod monic_kernelPolynomial kohelQuotient map_kohelQuotient deuringA₃ levelThreeModulus deuringA₃_eq_evalEval_polynomialY deuringA₃_eq_sub_negY levelThreeModulus_map_of_isUnit levelThreeModulus_variableChange Affine.vcXInv Affine.vcYInv Affine.vcX_vcXInv Affine.vcY_vcYInv Affine.nonsingular_variableChange_iff Affine.Point.vcInvFun map_levelThreeModulus_kohelQuotient_sub_ne_zero_of_map_j_ne_C exists_equation_and_eval_Psi3_eq_zero_and_map_eq_of_isAdicComplete exists_powerSeries_isElliptic_variableChange_smul_map_eq_and_map_j_ne_C kohelQuotient_kernelPolynomial_eq_veluQuotient separable_prePsi_of_isUnit Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi Affine.Point.vcInvFun_add"
p2m_open "WeierstrassCurve"

namespace DeuringDisc₃

section Hensel

theorem ker_constantCoeff (R : Type*) [CommRing R] :
    RingHom.ker (PowerSeries.constantCoeff (R := R)) = Ideal.span {PowerSeries.X} := by
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]

theorem isAdicComplete_ker_constantCoeff (R : Type*) [CommRing R] :
    IsAdicComplete (RingHom.ker (PowerSeries.constantCoeff (R := R))) (PowerSeries R) := by
  rw [ker_constantCoeff]; infer_instance

theorem isUnit_of_isUnit_map {R S : Type*} [CommRing R] [CommRing S] (ρ : R →+* S)
    (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ ≤ (⊥ : Ideal R).jacobson) {r : R}
    (hr : IsUnit (ρ r)) : IsUnit r := by
  obtain ⟨v, hv⟩ := hρ ↑(hr.unit⁻¹)
  have h1 : r * v - 1 ∈ RingHom.ker ρ := by
    rw [RingHom.mem_ker, map_sub, map_mul, hv, map_one, IsUnit.mul_val_inv, sub_self]
  have h2 := Ideal.mem_jacobson_bot.mp (hker h1) 1
  rw [mul_one, sub_add_cancel] at h2
  exact isUnit_of_mul_isUnit_left h2

variable {𝒪 : Type*} [CommRing 𝒪] {k : Type*} [Field k] (π : 𝒪 →+* k)
  (hπ : Function.Surjective π) [IsAdicComplete (RingHom.ker π) 𝒪]

local notation "cc" => (PowerSeries.constantCoeff (R := 𝒪))

include hπ

omit [IsAdicComplete (RingHom.ker π) 𝒪] in
theorem surjective_comp_constantCoeff : Function.Surjective (π.comp cc) := fun a => by
  obtain ⟨b, rfl⟩ := hπ a
  exact ⟨PowerSeries.C b, by simp⟩

theorem isUnit_of_isUnit_map₂ {x : PowerSeries 𝒪} (hx : IsUnit ((π.comp cc) x)) : IsUnit x := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  exact isUnit_of_isUnit_map π hπ (IsAdicComplete.le_jacobson_bot _) hx

theorem exists_factor_lift₂ {F : (PowerSeries 𝒪)[X]} (hF : F.Monic) {g₀ h₀ : k[X]}
    (hg₀ : g₀.Monic) (hh₀ : h₀.Monic) (hcop : IsCoprime g₀ h₀)
    (hF₀ : F.map (π.comp cc) = g₀ * h₀) :
    ∃ g h : (PowerSeries 𝒪)[X], g.Monic ∧ h.Monic ∧ g * h = F ∧ h.map (π.comp cc) = h₀ := by
  rw [← Polynomial.map_map] at hF₀
  obtain ⟨g₁, h₁, hg₁, hh₁, hgh₁, -, hh₁map, hcop₁, -⟩ :=
    Polynomial.exists_monic_mul_eq_and_map_eq_of_isCoprime_of_isAdicComplete π hπ (hF.map _)
      hg₀ hh₀ hcop hF₀
  haveI := isAdicComplete_ker_constantCoeff 𝒪
  obtain ⟨g, h, hg, hh, hgh, -, hhmap, -, -⟩ :=
    Polynomial.exists_monic_mul_eq_and_map_eq_of_isCoprime_of_isAdicComplete
      (PowerSeries.constantCoeff (R := 𝒪)) PowerSeries.constantCoeff_surj hF hg₁ hh₁ hcop₁
      hgh₁.symm
  exact ⟨g, h, hg, hh, hgh, by rw [← Polynomial.map_map, hhmap, hh₁map]⟩

theorem exists_threeTorsion_lift₂ (V : WeierstrassCurve (PowerSeries 𝒪)) (h3V : IsUnit (3 * V.Δ))
    {x₀ y₀ : k} (heq : (V.map (π.comp cc)).toAffine.Equation x₀ y₀)
    (hx₀ : (V.map (π.comp cc)).Ψ₃.eval x₀ = 0)
    (hy₀ : (V.map (π.comp cc)).deuringA₃ x₀ y₀ ≠ 0) :
    ∃ e f : PowerSeries 𝒪, V.toAffine.Equation e f ∧ V.Ψ₃.eval e = 0 ∧
      IsUnit (V.deuringA₃ e f) ∧
      π (PowerSeries.constantCoeff e) = x₀ ∧ π (PowerSeries.constantCoeff f) = y₀ := by
  set V₀ : WeierstrassCurve 𝒪 := V.map cc with hV₀
  have hV₀π : V₀.map π = V.map (π.comp cc) := by rw [hV₀, map_map]
  have h3V₀ : IsUnit (3 * V₀.Δ) := by
    rw [hV₀, map_Δ, ← map_ofNat cc 3, ← map_mul]; exact h3V.map _
  have heq' : (V₀.map π).toAffine.Equation x₀ y₀ := by rw [hV₀π]; exact heq
  have hx₀' : (V₀.map π).Ψ₃.eval x₀ = 0 := by rw [hV₀π]; exact hx₀
  have hy₀' : IsUnit ((V₀.map π).toAffine.polynomialY.evalEval x₀ y₀) := by
    rw [← deuringA₃_eq_evalEval_polynomialY, hV₀π]; exact isUnit_iff_ne_zero.mpr hy₀
  obtain ⟨b, c, hbc, hb, hbx, hcy, hu, -⟩ :=
    exists_equation_and_eval_Psi3_eq_zero_and_map_eq_of_isAdicComplete π hπ V₀ h3V₀ heq' hx₀' hy₀'
  haveI := isAdicComplete_ker_constantCoeff 𝒪
  obtain ⟨e, f, hef, he, heb, hfc, hu', -⟩ :=
    exists_equation_and_eval_Psi3_eq_zero_and_map_eq_of_isAdicComplete
      (PowerSeries.constantCoeff (R := 𝒪)) PowerSeries.constantCoeff_surj V h3V hbc hb hu
  refine ⟨e, f, hef, he, ?_, ?_, ?_⟩
  · rw [deuringA₃_eq_evalEval_polynomialY]; exact hu'
  · rw [heb]; exact hbx
  · rw [hfc]; exact hcy

end Hensel

section Field

variable {κ : Type*} [Field κ] [DecidableEq κ] {W : WeierstrassCurve κ}

theorem eq_or_eq_neg_of_fst_eq {x y y' : κ} (h : W.toAffine.Nonsingular x y)
    (h' : W.toAffine.Nonsingular x y') :
    Affine.Point.some x y' h' = Affine.Point.some x y h ∨
      Affine.Point.some x y' h' = -Affine.Point.some x y h := by
  by_cases hy : y' = W.toAffine.negY x y
  · right
    rw [Affine.Point.neg_some]
    simp only [hy]
  · left
    have := Affine.Y_eq_of_Y_ne h'.left h.left rfl hy
    subst this
    rfl

omit [DecidableEq κ] in
theorem exists_eq_some_of_ne_zero {P : W.toAffine.Point} (hP : P ≠ 0) :
    ∃ x y h, P = Affine.Point.some x y h ∧ P.coordsOrZero = (x, y) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · exact ⟨x, y, h, rfl, rfl⟩

variable (W)

theorem injOn_fst_oddOrderSummingSet (Q : W.toAffine.Point) (n : ℕ)
    (hQ : addOrderOf Q = 2 * n + 1) :
    Set.InjOn Prod.fst (W.oddOrderSummingSet Q n : Set (κ × κ)) := by
  intro P hP P' hP' hfst
  rw [Finset.mem_coe, mem_oddOrderSummingSet] at hP hP'
  obtain ⟨k, hk1, hkn, rfl⟩ := hP
  obtain ⟨l, hl1, hln, rfl⟩ := hP'
  have hk0 : k • Q ≠ 0 := nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)
  have hl0 : l • Q ≠ 0 := nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)
  obtain ⟨x, y, h, hkQ, hck⟩ := exists_eq_some_of_ne_zero hk0
  obtain ⟨x', y', h', hlQ, hcl⟩ := exists_eq_some_of_ne_zero hl0
  rw [hck, hcl] at hfst ⊢
  simp only at hfst
  subst hfst
  rcases eq_or_eq_neg_of_fst_eq h h' with e | e
  · rw [← hkQ, ← hlQ] at e
    rw [← hcl, ← hck, e]
  · exfalso
    rw [← hkQ, ← hlQ] at e
    have h0 : (k + l) • Q = 0 := by rw [add_nsmul, add_comm, e, neg_add_cancel]
    exact nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega) h0

theorem eval_preΨ'_eq_zero_of_mem_oddOrderSummingSet [W.IsElliptic] (Q : W.toAffine.Point) (n : ℕ)
    (hQ : addOrderOf Q = 2 * n + 1) {P : κ × κ} (hP : P ∈ W.oddOrderSummingSet Q n) :
    (W.preΨ' (2 * n + 1)).eval P.1 = 0 := by
  rw [mem_oddOrderSummingSet] at hP
  obtain ⟨k, hk1, hkn, rfl⟩ := hP
  have hk0 : k • Q ≠ 0 := nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)
  obtain ⟨x, y, h, hkQ, hck⟩ := exists_eq_some_of_ne_zero hk0
  rw [hck]
  have htor : (2 * n + 1) • Affine.Point.some x y h = 0 := by
    rw [← hkQ, ← mul_nsmul', ← hQ, mul_comm, mul_nsmul', addOrderOf_nsmul_eq_zero, nsmul_zero]
  exact (Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W ⟨n, rfl⟩ h).mp htor

theorem kernelPolynomial_dvd_preΨ' [W.IsElliptic] (Q : W.toAffine.Point) (n : ℕ)
    (hQ : addOrderOf Q = 2 * n + 1) (hm : ((2 * n + 1 : ℕ) : κ) ≠ 0) :
    kernelPolynomial (W.oddOrderSummingSet Q n) ∣ W.preΨ' (2 * n + 1) := by
  rw [kernelPolynomial_eq_multiset_prod,
    Multiset.prod_X_sub_C_dvd_iff_le_roots (W.preΨ'_ne_zero hm),
    Multiset.le_iff_subset]
  · intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨P, hP, rfl⟩ := hx
    rw [mem_roots (W.preΨ'_ne_zero hm), IsRoot.def]
    exact eval_preΨ'_eq_zero_of_mem_oddOrderSummingSet W Q n hQ (Finset.mem_val.mp hP)
  · exact Multiset.Nodup.map_on (fun P hP P' hP' h =>
      injOn_fst_oddOrderSummingSet W Q n hQ (Finset.mem_val.mp hP) (Finset.mem_val.mp hP') h)
      (Finset.nodup _)

theorem equation_of_mem_oddOrderSummingSet (Q : W.toAffine.Point) (n : ℕ)
    (hQ : addOrderOf Q = 2 * n + 1) {P : κ × κ} (hP : P ∈ W.oddOrderSummingSet Q n) :
    W.toAffine.Equation P.1 P.2 := by
  rw [mem_oddOrderSummingSet] at hP
  obtain ⟨k, hk1, hkn, rfl⟩ := hP
  have hk0 : k • Q ≠ 0 := nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)
  rcases hkQ : k • Q with _ | ⟨x, y, h⟩
  · exact absurd hkQ hk0
  · exact h.1

end Field

section ThreeTorsion

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

theorem deuringA₃_ne_zero_of_three_smul_eq_zero {x y : F} (h : W.toAffine.Nonsingular x y)
    (h3P : (3 : ℤ) • Affine.Point.some x y h = 0) : W.deuringA₃ x y ≠ 0 := by
  intro h0
  have hneg : -Affine.Point.some x y h = Affine.Point.some x y h := by
    rw [Affine.Point.neg_some]
    have hy : W.toAffine.negY x y = y := by
      rw [deuringA₃_eq_sub_negY, sub_eq_zero] at h0; exact h0.symm
    simp only [hy]
  have h2 : (2 : ℤ) • Affine.Point.some x y h = 0 := by
    rw [two_zsmul]
    nth_rw 1 [← hneg]
    rw [neg_add_cancel]
  have h1 : Affine.Point.some x y h = 0 := by
    have : ((3 : ℤ) - 2) • Affine.Point.some x y h = 0 := by
      rw [sub_zsmul, h3P, h2, neg_zero, add_zero]
    rwa [show (3 : ℤ) - 2 = 1 by norm_num, one_zsmul] at this
  exact Affine.Point.some_ne_zero h h1

theorem eval_Ψ₃_eq_zero_of_three_smul_eq_zero [W.IsElliptic] {x y : F}
    (h : W.toAffine.Nonsingular x y) (h3P : (3 : ℤ) • Affine.Point.some x y h = 0) :
    W.Ψ₃.eval x = 0 := by
  have h3 : (3 : ℕ) • Affine.Point.some x y h = 0 := by exact_mod_cast h3P
  rw [Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W (by decide) h, preΨ'_three] at h3
  exact h3

end ThreeTorsion

section VC

variable {F : Type*} [Field F] [DecidableEq F] (C : VariableChange F) (W : WeierstrassCurve F)

noncomputable def vcInvHom : W.toAffine.Point →+ (C • W).toAffine.Point where
  toFun := Affine.Point.vcInvFun C W
  map_zero' := rfl
  map_add' := Affine.Point.vcInvFun_add C W

@[scoped simp] theorem vcInvHom_apply (P : W.toAffine.Point) :
    vcInvHom C W P = Affine.Point.vcInvFun C W P := rfl

end VC

theorem main {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [CharZero 𝒪]
    {k : Type} [Field k] [IsAlgClosed k] [DecidableEq k]
    (π : 𝒪 →+* k) (hπ : Function.Surjective π) [IsAdicComplete (RingHom.ker π) 𝒪]
    (h3 : (3 : k) ≠ 0)
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (hm : ((2 * n + 1 : ℕ) : k) ≠ 0)
    (hsq : ¬ IsSquare (2 * n + 1)) (Q₀ : W.toAffine.Point) (hQ₀ : addOrderOf Q₀ = 2 * n + 1)
    (γ₀ : VariableChange k) (hγ₀ : γ₀ • W = W.veluQuotient (W.oddOrderSummingSet Q₀ n))
    {x₁ y₁ x₂ y₂ : k} (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hP₁ : (3 : ℤ) • Affine.Point.some x₁ y₁ h₁ = 0) (hP₂ : (3 : ℤ) • Affine.Point.some x₂ y₂ h₂ = 0)
    (hx : x₁ ≠ x₂) :
    ∃ (E : WeierstrassCurve (PowerSeries 𝒪)) (_ : E.IsElliptic)
      (_ : E.map (π.comp (PowerSeries.constantCoeff (R := 𝒪))) = W)
      (_ : PowerSeries.map π E.j ≠
        PowerSeries.C (PowerSeries.constantCoeff (PowerSeries.map π E.j)))
      (h : Polynomial (PowerSeries 𝒪)) (_ : h.Monic) (_ : h ∣ E.preΨ' (2 * n + 1))
      (_ : h.map (π.comp (PowerSeries.constantCoeff (R := 𝒪))) =
        kernelPolynomial (W.oddOrderSummingSet Q₀ n))
      (_ : (E.kohelQuotient h).IsElliptic)
      (_ : (E.kohelQuotient h).map (π.comp (PowerSeries.constantCoeff (R := 𝒪))) = γ₀ • W)
      (e₁ f₁ e₂ f₂ e'₁ f'₁ e'₂ f'₂ : PowerSeries 𝒪),
      E.toAffine.Equation e₁ f₁ ∧ E.toAffine.Equation e₂ f₂ ∧
      E.Ψ₃.eval e₁ = 0 ∧ E.Ψ₃.eval e₂ = 0 ∧
      IsUnit (E.deuringA₃ e₁ f₁) ∧ IsUnit (E.deuringA₃ e₂ f₂) ∧
      (E.kohelQuotient h).toAffine.Equation e'₁ f'₁ ∧ (E.kohelQuotient h).toAffine.Equation e'₂ f'₂ ∧
      (E.kohelQuotient h).Ψ₃.eval e'₁ = 0 ∧ (E.kohelQuotient h).Ψ₃.eval e'₂ = 0 ∧
      IsUnit ((E.kohelQuotient h).deuringA₃ e'₁ f'₁) ∧
      IsUnit ((E.kohelQuotient h).deuringA₃ e'₂ f'₂) ∧
      π (PowerSeries.constantCoeff e₁) = x₁ ∧ π (PowerSeries.constantCoeff f₁) = y₁ ∧
      π (PowerSeries.constantCoeff e₂) = x₂ ∧ π (PowerSeries.constantCoeff f₂) = y₂ ∧
      π (PowerSeries.constantCoeff e'₁) = Affine.vcXInv γ₀ x₁ ∧
      π (PowerSeries.constantCoeff f'₁) = Affine.vcYInv γ₀ x₁ y₁ ∧
      π (PowerSeries.constantCoeff e'₂) = Affine.vcXInv γ₀ x₂ ∧
      π (PowerSeries.constantCoeff f'₂) = Affine.vcYInv γ₀ x₂ y₂ ∧
      π (PowerSeries.constantCoeff ((E.kohelQuotient h).levelThreeModulus e'₁ f'₁ e'₂
        - E.levelThreeModulus e₁ f₁ e₂)) = 0 ∧
      PowerSeries.map π ((E.kohelQuotient h).levelThreeModulus e'₁ f'₁ e'₂
        - E.levelThreeModulus e₁ f₁ e₂) ≠ 0 := by
  classical

  set ρ : PowerSeries 𝒪 →+* k := π.comp (PowerSeries.constantCoeff (R := 𝒪)) with hρ_def
  have hρ : Function.Surjective ρ := surjective_comp_constantCoeff π hπ
  haveI : IsLocalHom π :=
    ⟨fun a ha => isUnit_of_isUnit_map π hπ (IsAdicComplete.le_jacobson_bot _) ha⟩
  set m : ℕ := 2 * n + 1 with hm_def

  obtain ⟨E₀, hE₀ell, ⟨v, hv⟩, hj₀⟩ :=
    exists_powerSeries_isElliptic_variableChange_smul_map_eq_and_map_j_ne_C π hπ W

  obtain ⟨u', hu'⟩ := hρ (v.u : k)
  have hu'unit : IsUnit u' := isUnit_of_isUnit_map₂ π hπ (by rw [hu']; exact v.u.isUnit)
  obtain ⟨r', hr'⟩ := hρ v.r
  obtain ⟨s', hs'⟩ := hρ v.s
  obtain ⟨t', ht'⟩ := hρ v.t
  let vT : VariableChange (PowerSeries 𝒪) := ⟨hu'unit.unit, r', s', t'⟩
  have hvT : vT.map ρ = v := by
    refine VariableChange.ext ?_ hr' hs' ht'
    ext
    rw [VariableChange.map_u]
    simp [vT, hu']
  obtain ⟨E, hEell, hE, hj⟩ : ∃ (E : WeierstrassCurve (PowerSeries 𝒪)) (_ : E.IsElliptic),
      E.map ρ = W ∧ PowerSeries.map π E.j ≠
        PowerSeries.C (PowerSeries.constantCoeff (PowerSeries.map π E.j)) := by
    refine ⟨vT • E₀, inferInstance, ?_, ?_⟩
    · rw [← map_variableChange, hvT, hv]
    · rw [variableChange_j]; exact hj₀
  subst hE

  have hmodd : Odd m := ⟨n, rfl⟩
  have hmR : IsUnit (m : PowerSeries 𝒪) :=
    isUnit_of_isUnit_map₂ π hπ (by rw [map_natCast]; exact isUnit_iff_ne_zero.mpr hm)
  set um := hmR.unit with hum
  set FΨ : (PowerSeries 𝒪)[X] := C (↑um⁻¹ : PowerSeries 𝒪) * E.preΨ' m with hFΨ_def
  have hlc : (E.preΨ' m).leadingCoeff = m := by
    rw [E.leadingCoeff_preΨ' hmR.ne_zero, if_neg (Nat.not_even_iff_odd.mpr hmodd)]
  have hFΨ : FΨ.Monic := monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [hlc]; exact um.inv_val)
  have hFΨdvd : FΨ ∣ E.preΨ' m := ⟨C (um : PowerSeries 𝒪), by
    rw [hFΨ_def, mul_comm, ← mul_assoc, ← C_mul, hum, IsUnit.unit_spec, IsUnit.mul_val_inv, C_1,
      one_mul]⟩
  set h₀ : k[X] := kernelPolynomial ((E.map ρ).oddOrderSummingSet Q₀ n) with hh₀
  have hh₀m : h₀.Monic := monic_kernelPolynomial _
  have hFΨ₀ : FΨ.map ρ = C (ρ ↑um⁻¹) * (E.map ρ).preΨ' m := by
    rw [hFΨ_def, Polynomial.map_mul, map_C, map_preΨ']
  have hsep : (FΨ.map ρ).Separable := by
    have h1 : ((E.map ρ).preΨ' m).Separable :=
      WeierstrassCurve.separable_prePsi_of_isUnit (E.map ρ) hmodd
        ((isUnit_iff_ne_zero.mpr hm).mul (E.map ρ).isUnit_Δ)
    refine h1.of_dvd ⟨C (ρ um), ?_⟩
    rw [hFΨ₀, mul_comm, ← mul_assoc, ← C_mul, ← map_mul, Units.mul_inv, map_one, C_1, one_mul]
  have hh₀dvd : h₀ ∣ FΨ.map ρ := by
    refine (kernelPolynomial_dvd_preΨ' (E.map ρ) Q₀ n hQ₀ hm).trans ⟨C (ρ ↑um⁻¹), ?_⟩
    rw [hFΨ₀, mul_comm]
  set g₀ : k[X] := FΨ.map ρ /ₘ h₀ with hg₀
  have hfac : FΨ.map ρ = g₀ * h₀ := by
    have := modByMonic_add_div (FΨ.map ρ) h₀
    rw [(modByMonic_eq_zero_iff_dvd hh₀m).mpr hh₀dvd, zero_add] at this
    rw [mul_comm]; exact this.symm
  have hg₀m : g₀.Monic := by
    have hFm : (FΨ.map ρ).Monic := hFΨ.map ρ
    rw [hfac] at hFm
    exact hh₀m.of_mul_monic_right hFm
  have hcop : IsCoprime g₀ h₀ := (hfac ▸ hsep).isCoprime
  obtain ⟨g, h, -, hh, hgh, hhmap⟩ := exists_factor_lift₂ π hπ hFΨ hg₀m hh₀m hcop hfac
  have hdvd : h ∣ E.preΨ' m := (Dvd.intro_left g hgh).trans hFΨdvd

  set E₁ : WeierstrassCurve (PowerSeries 𝒪) := E.kohelQuotient h with hE₁_def
  have hE₁ : E₁.map ρ = γ₀ • E.map ρ := by
    rw [hE₁_def, map_kohelQuotient E ρ hh, hhmap, hh₀,
      kohelQuotient_kernelPolynomial_eq_veluQuotient _ _
        (fun P hP => equation_of_mem_oddOrderSummingSet _ Q₀ n hQ₀ hP), hγ₀]
  haveI hE₁ell : E₁.IsElliptic := by
    refine ⟨isUnit_of_isUnit_map₂ π hπ ?_⟩
    rw [← hρ_def, ← map_Δ, hE₁]
    exact (γ₀ • E.map ρ).isUnit_Δ

  have h3R : IsUnit (3 : PowerSeries 𝒪) :=
    isUnit_of_isUnit_map₂ π hπ (by rw [map_ofNat]; exact isUnit_iff_ne_zero.mpr h3)
  have hlift : ∀ (V : WeierstrassCurve (PowerSeries 𝒪)) [V.IsElliptic] {x y : k}
      (hxy : (V.map ρ).toAffine.Nonsingular x y) (h3P : (3 : ℤ) • Affine.Point.some x y hxy = 0),
      ∃ e f : PowerSeries 𝒪, V.toAffine.Equation e f ∧ V.Ψ₃.eval e = 0 ∧
        IsUnit (V.deuringA₃ e f) ∧
        π (PowerSeries.constantCoeff e) = x ∧ π (PowerSeries.constantCoeff f) = y := by
    intro V _ x y hxy h3P
    haveI : (V.map ρ).IsElliptic := inferInstance
    exact exists_threeTorsion_lift₂ π hπ V (h3R.mul V.isUnit_Δ) hxy.1
      (eval_Ψ₃_eq_zero_of_three_smul_eq_zero hxy h3P)
      (deuringA₃_ne_zero_of_three_smul_eq_zero hxy h3P)
  obtain ⟨e₁, f₁, hef₁, he₁, hu₁, he₁₀, hf₁₀⟩ := hlift E h₁ hP₁
  obtain ⟨e₂, f₂, hef₂, he₂, hu₂, he₂₀, hf₂₀⟩ := hlift E h₂ hP₂

  let ι₀ := vcInvHom γ₀ (E.map ρ)
  have hι₀ : ∀ {x y : k} (hxy : (E.map ρ).toAffine.Nonsingular x y)
      (h3P : (3 : ℤ) • Affine.Point.some x y hxy = 0),
      ∃ hxy' : (E₁.map ρ).toAffine.Nonsingular (Affine.vcXInv γ₀ x) (Affine.vcYInv γ₀ x y),
        (3 : ℤ) • Affine.Point.some _ _ hxy' = 0 := by
    intro x y hxy h3P
    have hT : ι₀ (Affine.Point.some x y hxy) =
        Affine.Point.some (Affine.vcXInv γ₀ x) (Affine.vcYInv γ₀ x y)
          ((Affine.nonsingular_variableChange_iff _ _).mpr
            (by rwa [Affine.vcX_vcXInv, Affine.vcY_vcYInv])) := rfl
    have h3T : (3 : ℤ) • ι₀ (Affine.Point.some x y hxy) = 0 := by
      rw [← map_zsmul, h3P, map_zero]
    rw [hT] at h3T
    rw [hE₁]
    exact ⟨_, h3T⟩
  obtain ⟨h₁', hP₁'⟩ := hι₀ h₁ hP₁
  obtain ⟨h₂', hP₂'⟩ := hι₀ h₂ hP₂
  obtain ⟨e'₁, f'₁, hef'₁, he'₁, hu'₁, he'₁₀, hf'₁₀⟩ := hlift E₁ h₁' hP₁'
  obtain ⟨e'₂, f'₂, hef'₂, he'₂, hu'₂, he'₂₀, hf'₂₀⟩ := hlift E₁ h₂' hP₂'

  set x'₁ := Affine.vcXInv γ₀ x₁ with hx'₁
  set x'₂ := Affine.vcXInv γ₀ x₂ with hx'₂
  set y'₁ := Affine.vcYInv γ₀ x₁ y₁ with hy'₁
  have hx' : x'₁ ≠ x'₂ := by
    intro h12
    apply hx
    rw [← Affine.vcX_vcXInv (C := γ₀) x₁, ← Affine.vcX_vcXInv (C := γ₀) x₂]
    exact congrArg _ h12
  have hτ : (E.map ρ).levelThreeModulus x₁ y₁ x₂ = (E₁.map ρ).levelThreeModulus x'₁ y'₁ x'₂ := by
    rw [hE₁, ← levelThreeModulus_variableChange (W := E.map ρ) γ₀ x'₁ y'₁ x'₂]
    have ex₁ : (γ₀.u : k) ^ 2 * x'₁ + γ₀.r = x₁ := Affine.vcX_vcXInv (C := γ₀) x₁
    have ex₂ : (γ₀.u : k) ^ 2 * x'₂ + γ₀.r = x₂ := Affine.vcX_vcXInv (C := γ₀) x₂
    have ey₁ : (γ₀.u : k) ^ 3 * y'₁ + (γ₀.u : k) ^ 2 * γ₀.s * x'₁ + γ₀.t = y₁ :=
      Affine.vcY_vcYInv (C := γ₀) x₁ y₁
    rw [ex₁, ex₂, ey₁]
  have hG0 : π (PowerSeries.constantCoeff (E₁.levelThreeModulus e'₁ f'₁ e'₂
      - E.levelThreeModulus e₁ f₁ e₂)) = 0 := by
    change ρ _ = 0
    rw [map_sub, ← levelThreeModulus_map_of_isUnit ρ hu'₁, ← levelThreeModulus_map_of_isUnit ρ hu₁]
    have e1 : ρ e₁ = x₁ := he₁₀
    have e2 : ρ e₂ = x₂ := he₂₀
    have f1 : ρ f₁ = y₁ := hf₁₀
    have e1' : ρ e'₁ = x'₁ := he'₁₀
    have e2' : ρ e'₂ = x'₂ := he'₂₀
    have f1' : ρ f'₁ = y'₁ := hf'₁₀
    rw [e1, e2, f1, e1', e2', f1', hτ, sub_self]

  have hne : ∀ {a b : PowerSeries 𝒪} {x y : k}, π (PowerSeries.constantCoeff a) = x →
      π (PowerSeries.constantCoeff b) = y → x ≠ y → PowerSeries.map π (b - a) ≠ 0 := by
    intro a b x y ha hb hxy h0
    apply hxy
    have := congrArg (PowerSeries.constantCoeff (R := k)) h0
    rw [map_zero] at this
    change π (PowerSeries.constantCoeff (b - a)) = 0 at this
    rw [map_sub, map_sub, ha, hb, sub_eq_zero] at this
    exact this.symm
  have hG : PowerSeries.map π (E₁.levelThreeModulus e'₁ f'₁ e'₂
      - E.levelThreeModulus e₁ f₁ e₂) ≠ 0 :=
    map_levelThreeModulus_kohelQuotient_sub_ne_zero_of_map_j_ne_C π hπ h3 E hj hm hsq Q₀ hQ₀ hh
      hdvd (hhmap.trans hh₀) hef₁ he₁ he₂ hu₁ (hne he₁₀ he₂₀ hx) hef'₁ he'₁ he'₂ hu'₁
      (hne he'₁₀ he'₂₀ hx')
  exact ⟨E, inferInstance, rfl, hj, h, hh, hdvd, hhmap.trans hh₀, hE₁ell, hE₁, e₁, f₁, e₂, f₂,
    e'₁, f'₁, e'₂, f'₂, hef₁, hef₂, he₁, he₂, hu₁, hu₂, hef'₁, hef'₂, he'₁, he'₂, hu'₁, hu'₂,
    he₁₀, hf₁₀, he₂₀, hf₂₀, he'₁₀, hf'₁₀, he'₂₀, hf'₂₀, hG0, hG⟩

end DeuringDisc₃
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_powerSeries_deformation_kohelQuotient_threeTorsion_levelThreeModulus_of_smul_eq_veluQuotient.WeierstrassCurve.DeuringDisc₃"

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_powerSeries_deformation_kohelQuotient_threeTorsion_levelThreeModulus_of_smul_eq_veluQuotient.WeierstrassCurve.DeuringDisc₃ P2MW.S_WeierstrassCurve_exists_powerSeries_deformation_kohelQuotient_threeTorsion_levelThreeModulus_of_smul_eq_veluQuotient.WeierstrassCurve"

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [CharZero 𝒪]
    {k : Type} [Field k] [IsAlgClosed k] [DecidableEq k]
    (π : 𝒪 →+* k) (hπ : Function.Surjective π) [IsAdicComplete (RingHom.ker π) 𝒪]
    (h3 : (3 : k) ≠ 0)
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (hm : ((2 * n + 1 : ℕ) : k) ≠ 0)
    (hsq : ¬ IsSquare (2 * n + 1)) (Q₀ : W.toAffine.Point) (hQ₀ : addOrderOf Q₀ = 2 * n + 1)
    (γ₀ : WeierstrassCurve.VariableChange k)
    (hγ₀ : γ₀ • W = W.veluQuotient (W.oddOrderSummingSet Q₀ n))
    {x₁ y₁ x₂ y₂ : k} (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hP₁ : (3 : ℤ) • (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) = 0)
    (hP₂ : (3 : ℤ) • (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) = 0)
    (hx : x₁ ≠ x₂) :
    ∃ (E : WeierstrassCurve (PowerSeries 𝒪)) (_ : E.IsElliptic)
      (_ : E.map (π.comp (PowerSeries.constantCoeff (R := 𝒪))) = W)
      (_ : PowerSeries.map π E.j ≠
        PowerSeries.C (PowerSeries.constantCoeff (PowerSeries.map π E.j)))
      (h : Polynomial (PowerSeries 𝒪)) (_ : h.Monic) (_ : h ∣ E.preΨ' (2 * n + 1))
      (_ : h.map (π.comp (PowerSeries.constantCoeff (R := 𝒪))) =
        WeierstrassCurve.kernelPolynomial (W.oddOrderSummingSet Q₀ n))
      (_ : (E.kohelQuotient h).IsElliptic)
      (_ : (E.kohelQuotient h).map (π.comp (PowerSeries.constantCoeff (R := 𝒪))) = γ₀ • W)
      (e₁ f₁ e₂ f₂ e'₁ f'₁ e'₂ f'₂ : PowerSeries 𝒪),
      E.toAffine.Equation e₁ f₁ ∧ E.toAffine.Equation e₂ f₂ ∧
      E.Ψ₃.eval e₁ = 0 ∧ E.Ψ₃.eval e₂ = 0 ∧
      IsUnit (E.deuringA₃ e₁ f₁) ∧ IsUnit (E.deuringA₃ e₂ f₂) ∧
      (E.kohelQuotient h).toAffine.Equation e'₁ f'₁ ∧
      (E.kohelQuotient h).toAffine.Equation e'₂ f'₂ ∧
      (E.kohelQuotient h).Ψ₃.eval e'₁ = 0 ∧ (E.kohelQuotient h).Ψ₃.eval e'₂ = 0 ∧
      IsUnit ((E.kohelQuotient h).deuringA₃ e'₁ f'₁) ∧
      IsUnit ((E.kohelQuotient h).deuringA₃ e'₂ f'₂) ∧
      π (PowerSeries.constantCoeff e₁) = x₁ ∧ π (PowerSeries.constantCoeff f₁) = y₁ ∧
      π (PowerSeries.constantCoeff e₂) = x₂ ∧ π (PowerSeries.constantCoeff f₂) = y₂ ∧
      π (PowerSeries.constantCoeff e'₁) = WeierstrassCurve.Affine.vcXInv γ₀ x₁ ∧
      π (PowerSeries.constantCoeff f'₁) = WeierstrassCurve.Affine.vcYInv γ₀ x₁ y₁ ∧
      π (PowerSeries.constantCoeff e'₂) = WeierstrassCurve.Affine.vcXInv γ₀ x₂ ∧
      π (PowerSeries.constantCoeff f'₂) = WeierstrassCurve.Affine.vcYInv γ₀ x₂ y₂ ∧
      π (PowerSeries.constantCoeff ((E.kohelQuotient h).levelThreeModulus e'₁ f'₁ e'₂
        - E.levelThreeModulus e₁ f₁ e₂)) = 0 ∧
      PowerSeries.map π ((E.kohelQuotient h).levelThreeModulus e'₁ f'₁ e'₂
        - E.levelThreeModulus e₁ f₁ e₂) ≠ 0 :=
  WeierstrassCurve.DeuringDisc₃.main π hπ h3 W n hm hsq Q₀ hQ₀ γ₀ hγ₀ h₁ h₂ hP₁ hP₂ hx

end S_WeierstrassCurve_exists_powerSeries_deformation_kohelQuotient_threeTorsion_levelThreeModulus_of_smul_eq_veluQuotient
end P2MW
export P2MW.S_WeierstrassCurve_exists_powerSeries_deformation_kohelQuotient_threeTorsion_levelThreeModulus_of_smul_eq_veluQuotient (solution)
