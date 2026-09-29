-- Prove2me | solution 1 for WeierstrassCurve.exists_powerSeries_deformation_kohelQuotient_twoTorsion_legendreCross_of_smul_eq_veluQuotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/0f568ad3-e830-55e5-a479-af4a46fd2673

import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_WeierstrassCurve_KernelPolynomial
import Definitions.Def_WeierstrassCurve_KohelQuotient
import Definitions.Def_WeierstrassCurve_LegendreModulus
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_map_legendreCross_kohelQuotient_ne_zero_of_map_j_ne_C
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

namespace P2MW.S_WeierstrassCurve_exists_powerSeries_deformation_kohelQuotient_twoTorsion_legendreCross_of_smul_eq_veluQuotient
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
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY Affine.Y_eq_of_Y_ne variableChange_j VariableChange.ext a₃ map_map a₁ preΨ'_ne_zero map map_b₂ b₂ mk Ψ₂Sq a₄ a₂ Affine.Point.some Affine.nonsingular_iff' Affine.Point.some.injEq leadingCoeff_preΨ' map_preΨ' leadingCoeff_Ψ₂Sq VariableChange.map_u preΨ' toAffine Affine.Point map_Δ b₆ VariableChange Affine.equation_iff Affine.Point.neg_some map_Ψ₂Sq map_variableChange j b₄ veluQuotient oddOrderSummingSet mem_oddOrderSummingSet kernelPolynomial kernelPolynomial_eq_multiset_prod monic_kernelPolynomial kohelQuotient map_kohelQuotient legendreLambda legendreLambda_def legendreLambda_variableChange Affine.vcXInv Affine.vcYInv Affine.vcX_vcXInv Affine.vcY_vcYInv Affine.nonsingular_variableChange_iff Affine.Point.vcInvFun map_legendreCross_kohelQuotient_ne_zero_of_map_j_ne_C exists_powerSeries_isElliptic_variableChange_smul_map_eq_and_map_j_ne_C kohelQuotient_kernelPolynomial_eq_veluQuotient separable_prePsi_of_isUnit Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi Affine.Point.vcInvFun_add"
p2m_open "WeierstrassCurve"

namespace DeuringDisc

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

theorem exists_root_lift {R S : Type*} [CommRing R] [CommRing S] (ρ : R →+* S)
    (hρ : Function.Surjective ρ) [IsAdicComplete (RingHom.ker ρ) R]
    {f : R[X]} (hf : f.Monic) {a₀ : S} (ha : (f.map ρ).eval a₀ = 0)
    (ha' : IsUnit ((f.map ρ).derivative.eval a₀)) :
    ∃ a : R, f.eval a = 0 ∧ ρ a = a₀ := by
  obtain ⟨b, rfl⟩ := hρ a₀
  have h1 : f.eval b ∈ RingHom.ker ρ := by
    rw [RingHom.mem_ker, ← eval₂_hom, ← eval_map, ha]
  have h2 : IsUnit (Ideal.Quotient.mk (RingHom.ker ρ) (f.derivative.eval b)) := by
    let e := RingHom.quotientKerEquivOfSurjective hρ
    have h3 : e (Ideal.Quotient.mk (RingHom.ker ρ) (f.derivative.eval b)) = ρ (f.derivative.eval b) :=
      RingHom.quotientKerEquivOfSurjective_apply_mk hρ _
    have h4 : IsUnit (ρ (f.derivative.eval b)) := by
      rw [derivative_map, eval_map, eval₂_hom] at ha'
      exact ha'
    rw [← h3] at h4
    simpa using h4.map e.symm
  obtain ⟨a, ha1, ha2⟩ := HenselianRing.is_henselian (I := RingHom.ker ρ) f hf b h1 h2
  refine ⟨a, ha1, ?_⟩
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at ha2
  exact ha2

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

theorem exists_root_lift₂ {f : (PowerSeries 𝒪)[X]} (hf : f.Monic) {a₀ : k}
    (ha : (f.map (π.comp cc)).eval a₀ = 0) (ha' : (f.map (π.comp cc)).derivative.eval a₀ ≠ 0) :
    ∃ a : PowerSeries 𝒪, f.eval a = 0 ∧ π (PowerSeries.constantCoeff a) = a₀ := by
  have hf₁ : (f.map cc).Monic := hf.map _
  rw [← Polynomial.map_map] at ha ha'
  obtain ⟨b, hb, hb₀⟩ := exists_root_lift π hπ hf₁ ha (isUnit_iff_ne_zero.mpr ha')
  haveI := isAdicComplete_ker_constantCoeff 𝒪
  have hb' : IsUnit (((f.map cc).derivative).eval b) := by
    refine isUnit_of_isUnit_map π hπ (IsAdicComplete.le_jacobson_bot _) ?_
    rw [← eval₂_hom, ← eval_map, ← derivative_map, hb₀]
    exact isUnit_iff_ne_zero.mpr ha'
  obtain ⟨a, ha1, ha2⟩ := exists_root_lift (PowerSeries.constantCoeff (R := 𝒪))
    PowerSeries.constantCoeff_surj hf hb hb'
  exact ⟨a, ha1, by rw [ha2, hb₀]⟩

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

section TwoTorsion

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

omit [DecidableEq F] in
theorem eval_Ψ₂Sq (x : F) :
    W.Ψ₂Sq.eval x = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  simp only [Ψ₂Sq, eval_add, eval_mul, eval_C, eval_pow, eval_X]

omit [DecidableEq F] in
theorem eval_derivative_Ψ₂Sq (x : F) :
    W.Ψ₂Sq.derivative.eval x = 12 * x ^ 2 + 2 * W.b₂ * x + 2 * W.b₄ := by
  simp only [Ψ₂Sq, derivative_add, derivative_mul, derivative_C, derivative_X_pow,
    derivative_X, zero_mul, zero_add, eval_add, eval_mul, eval_C, eval_pow, eval_X,
    Nat.cast_ofNat, add_zero, mul_one]
  ring

variable {W}

theorem two_mul_Y_add_eq_zero_of_two_smul_eq_zero {x y : F} (h : W.toAffine.Nonsingular x y)
    (h2P : (2 : ℤ) • Affine.Point.some x y h = 0) : 2 * y + W.a₁ * x + W.a₃ = 0 := by
  rw [two_zsmul, add_eq_zero_iff_eq_neg, Affine.Point.neg_some, Affine.Point.some.injEq] at h2P
  have hy := h2P.2
  simp only [Affine.negY] at hy
  linear_combination hy

theorem eval_Ψ₂Sq_eq_zero_of_two_smul_eq_zero {x y : F} (h : W.toAffine.Nonsingular x y)
    (h2P : (2 : ℤ) • Affine.Point.some x y h = 0) : W.Ψ₂Sq.eval x = 0 := by
  have hy := two_mul_Y_add_eq_zero_of_two_smul_eq_zero h h2P
  have heq := h.1
  rw [Affine.equation_iff] at heq
  rw [eval_Ψ₂Sq]
  simp only [b₂, b₄, b₆]
  have : (2 * y + W.a₁ * x + W.a₃) ^ 2 = 0 := by rw [hy]; ring
  linear_combination -4 * heq + this

theorem eval_derivative_Ψ₂Sq_ne_zero_of_two_smul_eq_zero (h2 : (2 : F) ≠ 0) {x y : F}
    (h : W.toAffine.Nonsingular x y) (h2P : (2 : ℤ) • Affine.Point.some x y h = 0) :
    W.Ψ₂Sq.derivative.eval x ≠ 0 := by
  have hy := two_mul_Y_add_eq_zero_of_two_smul_eq_zero h h2P
  have hns := (Affine.nonsingular_iff' x y).mp h
  rcases hns.2 with hX | hY
  · intro h0
    apply hX
    rw [eval_derivative_Ψ₂Sq] at h0
    simp only [b₂, b₄] at h0
    have h4 : (4 : F) ≠ 0 := by
      rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
    apply mul_left_cancel₀ h4
    change 4 * (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) = 4 * 0
    linear_combination -h0 + 2 * W.a₁ * hy
  · exact absurd hy hY

end TwoTorsion

theorem legendreLambda_eq {F : Type*} [Field F] (W : WeierstrassCurve F) (h2 : (2 : F) ≠ 0)
    {x₁ x₂ : F} (hx : x₁ ≠ x₂) :
    W.legendreLambda x₁ x₂ = (-W.b₂ - 8 * x₁ - 4 * x₂) / (4 * (x₂ - x₁)) := by
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hx' : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  rw [legendreLambda_def]
  field_simp
  ring

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
    (h2 : (2 : k) ≠ 0)
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (hm : ((2 * n + 1 : ℕ) : k) ≠ 0)
    (hsq : ¬ IsSquare (2 * n + 1)) (Q₀ : W.toAffine.Point) (hQ₀ : addOrderOf Q₀ = 2 * n + 1)
    (γ₀ : VariableChange k) (hγ₀ : γ₀ • W = W.veluQuotient (W.oddOrderSummingSet Q₀ n))
    {x₁ y₁ x₂ y₂ : k} (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hP₁ : (2 : ℤ) • Affine.Point.some x₁ y₁ h₁ = 0) (hP₂ : (2 : ℤ) • Affine.Point.some x₂ y₂ h₂ = 0)
    (hx : x₁ ≠ x₂) :
    ∃ (E : WeierstrassCurve (PowerSeries 𝒪)) (_ : E.IsElliptic)
      (_ : E.map (π.comp (PowerSeries.constantCoeff (R := 𝒪))) = W)
      (_ : PowerSeries.map π E.j ≠
        PowerSeries.C (PowerSeries.constantCoeff (PowerSeries.map π E.j)))
      (h : Polynomial (PowerSeries 𝒪)) (_ : h.Monic) (_ : h ∣ E.preΨ' (2 * n + 1))
      (_ : h.map (π.comp (PowerSeries.constantCoeff (R := 𝒪))) =
        kernelPolynomial (W.oddOrderSummingSet Q₀ n))
      (_ : (E.kohelQuotient h).IsElliptic)
      (e₁ e₂ e'₁ e'₂ : PowerSeries 𝒪),
      E.Ψ₂Sq.eval e₁ = 0 ∧ E.Ψ₂Sq.eval e₂ = 0 ∧
      (E.kohelQuotient h).Ψ₂Sq.eval e'₁ = 0 ∧ (E.kohelQuotient h).Ψ₂Sq.eval e'₂ = 0 ∧
      π (PowerSeries.constantCoeff e₁) = x₁ ∧ π (PowerSeries.constantCoeff e₂) = x₂ ∧
      π (PowerSeries.constantCoeff e'₁) = Affine.vcXInv γ₀ x₁ ∧
      π (PowerSeries.constantCoeff e'₂) = Affine.vcXInv γ₀ x₂ ∧
      π (PowerSeries.constantCoeff ((-E.b₂ - 8 * e₁ - 4 * e₂) * (e'₂ - e'₁)
        - (-(E.kohelQuotient h).b₂ - 8 * e'₁ - 4 * e'₂) * (e₂ - e₁))) = 0 ∧
      PowerSeries.map π ((-E.b₂ - 8 * e₁ - 4 * e₂) * (e'₂ - e'₁)
        - (-(E.kohelQuotient h).b₂ - 8 * e'₁ - 4 * e'₂) * (e₂ - e₁)) ≠ 0 := by
  classical

  set ρ : PowerSeries 𝒪 →+* k := π.comp (PowerSeries.constantCoeff (R := 𝒪)) with hρ_def
  have hρ : Function.Surjective ρ := surjective_comp_constantCoeff π hπ
  have hρC : ∀ a : 𝒪, ρ (PowerSeries.C a) = π a := fun a => by simp [hρ_def]
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

  have h4 : (4 : PowerSeries 𝒪) ≠ 0 := by
    intro h40
    apply h2
    have := congrArg ρ h40
    rw [map_ofNat, map_zero, show (4 : k) = 2 * 2 by norm_num] at this
    exact (mul_self_eq_zero.mp this)

  have hroot : ∀ (V : WeierstrassCurve (PowerSeries 𝒪)) [V.IsElliptic] {x y : k}
      (hxy : (V.map ρ).toAffine.Nonsingular x y) (h2P : (2 : ℤ) • Affine.Point.some x y hxy = 0),
      ∃ e : PowerSeries 𝒪, V.Ψ₂Sq.eval e = 0 ∧ π (PowerSeries.constantCoeff e) = x := by
    intro V _ x y hxy h2P
    have h4V : IsUnit (4 : PowerSeries 𝒪) := isUnit_of_isUnit_map₂ π hπ (by
      rw [map_ofNat, show (4 : k) = 2 * 2 by norm_num]
      exact (isUnit_iff_ne_zero.mpr h2).mul (isUnit_iff_ne_zero.mpr h2))
    set u4 := h4V.unit with hu4
    set f : (PowerSeries 𝒪)[X] := C (↑u4⁻¹ : PowerSeries 𝒪) * V.Ψ₂Sq with hf_def
    have hf : f.Monic := monic_C_mul_of_mul_leadingCoeff_eq_one (by
      rw [V.leadingCoeff_Ψ₂Sq h4V.ne_zero]; exact u4.inv_val)
    have hfmap : f.map ρ = C (ρ ↑u4⁻¹) * (V.map ρ).Ψ₂Sq := by
      rw [hf_def, Polynomial.map_mul, map_C, map_Ψ₂Sq]
    have hx0 : (f.map ρ).eval x = 0 := by
      rw [hfmap, eval_mul, eval_C, eval_Ψ₂Sq_eq_zero_of_two_smul_eq_zero hxy h2P, mul_zero]
    have hx1 : (f.map ρ).derivative.eval x ≠ 0 := by
      rw [hfmap, derivative_C_mul, eval_mul, eval_C]
      refine mul_ne_zero ?_ (eval_derivative_Ψ₂Sq_ne_zero_of_two_smul_eq_zero h2 hxy h2P)
      exact (Units.map (ρ : PowerSeries 𝒪 →* k) u4⁻¹).ne_zero
    obtain ⟨e, he, he₀⟩ := exists_root_lift₂ π hπ hf hx0 hx1
    refine ⟨e, ?_, he₀⟩
    rw [hf_def, eval_mul, eval_C] at he
    exact (mul_eq_zero.mp he).resolve_left (Units.ne_zero _)
  obtain ⟨e₁, he₁, he₁₀⟩ := hroot E h₁ hP₁
  obtain ⟨e₂, he₂, he₂₀⟩ := hroot E h₂ hP₂

  let ι₀ := vcInvHom γ₀ (E.map ρ)
  have hι₀ : ∀ {x y : k} (hxy : (E.map ρ).toAffine.Nonsingular x y)
      (h2P : (2 : ℤ) • Affine.Point.some x y hxy = 0),
      ∃ hxy' : (E₁.map ρ).toAffine.Nonsingular (Affine.vcXInv γ₀ x) (Affine.vcYInv γ₀ x y),
        (2 : ℤ) • Affine.Point.some _ _ hxy' = 0 := by
    intro x y hxy h2P
    have hT : ι₀ (Affine.Point.some x y hxy) =
        Affine.Point.some (Affine.vcXInv γ₀ x) (Affine.vcYInv γ₀ x y)
          ((Affine.nonsingular_variableChange_iff _ _).mpr
            (by rwa [Affine.vcX_vcXInv, Affine.vcY_vcYInv])) := rfl
    have h2T : (2 : ℤ) • ι₀ (Affine.Point.some x y hxy) = 0 := by
      rw [← map_zsmul, h2P, map_zero]
    rw [hT] at h2T
    rw [hE₁]
    exact ⟨_, h2T⟩
  obtain ⟨h₁', hP₁'⟩ := hι₀ h₁ hP₁
  obtain ⟨h₂', hP₂'⟩ := hι₀ h₂ hP₂
  obtain ⟨e'₁, he'₁, he'₁₀⟩ := hroot E₁ h₁' hP₁'
  obtain ⟨e'₂, he'₂, he'₂₀⟩ := hroot E₁ h₂' hP₂'

  set x'₁ := Affine.vcXInv γ₀ x₁ with hx'₁
  set x'₂ := Affine.vcXInv γ₀ x₂ with hx'₂
  have hx' : x'₁ ≠ x'₂ := by
    intro h12
    apply hx
    rw [← Affine.vcX_vcXInv (C := γ₀) x₁, ← Affine.vcX_vcXInv (C := γ₀) x₂]
    exact congrArg _ h12
  have hlam : (E.map ρ).legendreLambda x₁ x₂ = (E₁.map ρ).legendreLambda x'₁ x'₂ := by
    rw [hE₁, ← legendreLambda_variableChange h2 γ₀ (E.map ρ) x'₁ x'₂]
    congr 1
    · exact (Affine.vcX_vcXInv (C := γ₀) x₁).symm
    · exact (Affine.vcX_vcXInv (C := γ₀) x₂).symm
  have h4k : (4 : k) ≠ 0 := by
    rw [show (4 : k) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hF0 : π (PowerSeries.constantCoeff ((-E.b₂ - 8 * e₁ - 4 * e₂) * (e'₂ - e'₁)
      - (-E₁.b₂ - 8 * e'₁ - 4 * e'₂) * (e₂ - e₁))) = 0 := by
    rw [legendreLambda_eq _ h2 hx, legendreLambda_eq _ h2 hx',
      div_eq_div_iff (mul_ne_zero h4k (sub_ne_zero.mpr (Ne.symm hx)))
        (mul_ne_zero h4k (sub_ne_zero.mpr (Ne.symm hx'))), map_b₂, map_b₂] at hlam
    change ρ _ = 0
    simp only [map_sub, map_mul, map_neg, map_ofNat]
    have e1 : ρ e₁ = x₁ := he₁₀
    have e2 : ρ e₂ = x₂ := he₂₀
    have e1' : ρ e'₁ = x'₁ := he'₁₀
    have e2' : ρ e'₂ = x'₂ := he'₂₀
    rw [e1, e2, e1', e2']
    apply mul_left_cancel₀ h4k
    linear_combination hlam

  have hne : ∀ {a b : PowerSeries 𝒪} {x y : k}, π (PowerSeries.constantCoeff a) = x →
      π (PowerSeries.constantCoeff b) = y → x ≠ y → PowerSeries.map π (b - a) ≠ 0 := by
    intro a b x y ha hb hxy h0
    apply hxy
    have := congrArg (PowerSeries.constantCoeff (R := k)) h0
    rw [map_zero] at this
    change π (PowerSeries.constantCoeff (b - a)) = 0 at this
    rw [map_sub, map_sub, ha, hb, sub_eq_zero] at this
    exact this.symm
  have hF : PowerSeries.map π ((-E.b₂ - 8 * e₁ - 4 * e₂) * (e'₂ - e'₁)
      - (-E₁.b₂ - 8 * e'₁ - 4 * e'₂) * (e₂ - e₁)) ≠ 0 :=
    map_legendreCross_kohelQuotient_ne_zero_of_map_j_ne_C π hπ h2 E hj hm hsq Q₀ hQ₀ hh hdvd
      (hhmap.trans hh₀) he₁ he₂ (hne he₁₀ he₂₀ hx) he'₁ he'₂ (hne he'₁₀ he'₂₀ hx')
  exact ⟨E, inferInstance, rfl, hj, h, hh, hdvd, hhmap.trans hh₀, hE₁ell, e₁, e₂, e'₁, e'₂,
    he₁, he₂, he'₁, he'₂, he₁₀, he₂₀, he'₁₀, he'₂₀, hF0, hF⟩

end DeuringDisc
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_powerSeries_deformation_kohelQuotient_twoTorsion_legendreCross_of_smul_eq_veluQuotient.WeierstrassCurve.DeuringDisc"

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_powerSeries_deformation_kohelQuotient_twoTorsion_legendreCross_of_smul_eq_veluQuotient.WeierstrassCurve.DeuringDisc P2MW.S_WeierstrassCurve_exists_powerSeries_deformation_kohelQuotient_twoTorsion_legendreCross_of_smul_eq_veluQuotient.WeierstrassCurve"

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [CharZero 𝒪]
    {k : Type} [Field k] [IsAlgClosed k] [DecidableEq k]
    (π : 𝒪 →+* k) (hπ : Function.Surjective π) [IsAdicComplete (RingHom.ker π) 𝒪]
    (h2 : (2 : k) ≠ 0)
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (hm : ((2 * n + 1 : ℕ) : k) ≠ 0)
    (hsq : ¬ IsSquare (2 * n + 1)) (Q₀ : W.toAffine.Point) (hQ₀ : addOrderOf Q₀ = 2 * n + 1)
    (γ₀ : WeierstrassCurve.VariableChange k)
    (hγ₀ : γ₀ • W = W.veluQuotient (W.oddOrderSummingSet Q₀ n))
    {x₁ y₁ x₂ y₂ : k} (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hP₁ : (2 : ℤ) • (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) = 0)
    (hP₂ : (2 : ℤ) • (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) = 0)
    (hx : x₁ ≠ x₂) :
    ∃ (E : WeierstrassCurve (PowerSeries 𝒪)) (_ : E.IsElliptic)
      (_ : E.map (π.comp (PowerSeries.constantCoeff (R := 𝒪))) = W)
      (_ : PowerSeries.map π E.j ≠
        PowerSeries.C (PowerSeries.constantCoeff (PowerSeries.map π E.j)))
      (h : Polynomial (PowerSeries 𝒪)) (_ : h.Monic) (_ : h ∣ E.preΨ' (2 * n + 1))
      (_ : h.map (π.comp (PowerSeries.constantCoeff (R := 𝒪))) =
        WeierstrassCurve.kernelPolynomial (W.oddOrderSummingSet Q₀ n))
      (_ : (E.kohelQuotient h).IsElliptic)
      (e₁ e₂ e'₁ e'₂ : PowerSeries 𝒪),
      E.Ψ₂Sq.eval e₁ = 0 ∧ E.Ψ₂Sq.eval e₂ = 0 ∧
      (E.kohelQuotient h).Ψ₂Sq.eval e'₁ = 0 ∧ (E.kohelQuotient h).Ψ₂Sq.eval e'₂ = 0 ∧
      π (PowerSeries.constantCoeff e₁) = x₁ ∧ π (PowerSeries.constantCoeff e₂) = x₂ ∧
      π (PowerSeries.constantCoeff e'₁) = WeierstrassCurve.Affine.vcXInv γ₀ x₁ ∧
      π (PowerSeries.constantCoeff e'₂) = WeierstrassCurve.Affine.vcXInv γ₀ x₂ ∧
      π (PowerSeries.constantCoeff ((-E.b₂ - 8 * e₁ - 4 * e₂) * (e'₂ - e'₁)
        - (-(E.kohelQuotient h).b₂ - 8 * e'₁ - 4 * e'₂) * (e₂ - e₁))) = 0 ∧
      PowerSeries.map π ((-E.b₂ - 8 * e₁ - 4 * e₂) * (e'₂ - e'₁)
        - (-(E.kohelQuotient h).b₂ - 8 * e'₁ - 4 * e'₂) * (e₂ - e₁)) ≠ 0 :=
  WeierstrassCurve.DeuringDisc.main π hπ h2 W n hm hsq Q₀ hQ₀ γ₀ hγ₀ h₁ h₂ hP₁ hP₂ hx

end S_WeierstrassCurve_exists_powerSeries_deformation_kohelQuotient_twoTorsion_legendreCross_of_smul_eq_veluQuotient
end P2MW
export P2MW.S_WeierstrassCurve_exists_powerSeries_deformation_kohelQuotient_twoTorsion_legendreCross_of_smul_eq_veluQuotient (solution)
