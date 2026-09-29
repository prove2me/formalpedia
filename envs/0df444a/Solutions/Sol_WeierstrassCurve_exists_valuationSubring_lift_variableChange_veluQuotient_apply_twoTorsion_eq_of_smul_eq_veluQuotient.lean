-- Prove2me | solution 1 for WeierstrassCurve.exists_valuationSubring_lift_variableChange_veluQuotient_apply_twoTorsion_eq_of_smul_eq_veluQuotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/9230a4e7-7198-52ad-89e6-9ca7c43c115b

import Mathlib
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_RatPointHom
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_WeierstrassCurve_KernelPolynomial
import Definitions.Def_WeierstrassCurve_KohelQuotient
import Definitions.Def_WeierstrassCurve_LegendreModulus
import Theorems.Thm_WeierstrassCurve_exists_powerSeries_deformation_kohelQuotient_twoTorsion_legendreCross_of_smul_eq_veluQuotient
import Theorems.Thm_WittVector_exists_valuationSubring_residueField_equiv_of_isAlgebraic
import Theorems.Thm_PowerSeries_exists_ringHom_valuationSubring_map_eq_zero_of_constantCoeff_mem_maximalIdeal
import Theorems.Thm_WeierstrassCurve_exists_reduceHom_eq_and_map_eq_kernelPolynomial_oddOrderSummingSet
import Theorems.Thm_WeierstrassCurve_kohelQuotient_kernelPolynomial_eq_veluQuotient
import Theorems.Thm_ValuationSubring_henselianLocalRing_of_isAlgClosed
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_WeierstrassCurve_exists_variableChange_of_legendreLambda_eq
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_valuationSubring_lift_variableChange_veluQuotient_apply_twoTorsion_eq_of_smul_eq_veluQuotient
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom"
p2m_attr_erase "simp" "AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluY_empty WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false

open Polynomial IsLocalRing

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY Affine.Y_eq_of_Y_ne a₃ map_map a₁ map map_b₂ b₂ Ψ₂Sq a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq map_preΨ' reduction preΨ' toAffine Affine.Point map_injective map_Δ b₆ Affine.equation_iff_nonsingular Δ VariableChange Affine.equation_iff Affine.Point.neg_some map_Ψ₂Sq j b₄ reduceHom Affine.Y_mem_of_X_mem Affine.nonsingular_residue reducePoint reducePoint_some_of_mem Affine.vcX Affine.vcY Affine.vcXInv Affine.vcYInv Affine.vcX_vcXInv Affine.Point.vcFun Affine.Point.vcInvFun Affine.Point.vcFun_leftInverse Affine.Point.vcFun_rightInverse Affine.Point.equivOfVariableChangeEq ratPointMap_zero ratPointMap_some ratPointMap_injective ratPointHom ratPointMap veluQuotient Affine.Point.coordsOrZero Affine.Point.coordsOrZero_some oddOrderSummingSet mem_oddOrderSummingSet kernelPolynomial map_kernelPolynomial_of_injOn kohelQuotient map_kohelQuotient legendreLambda legendreLambda_def exists_powerSeries_deformation_kohelQuotient_twoTorsion_legendreCross_of_smul_eq_veluQuotient exists_reduceHom_eq_and_map_eq_kernelPolynomial_oddOrderSummingSet kohelQuotient_kernelPolynomial_eq_veluQuotient exists_variableChange_of_legendreLambda_eq Affine.Point.vcInvFun_add"
p2m_open "WeierstrassCurve"

namespace DeuringMarkedLift

section VC

variable {F : Type*} [Field F] [DecidableEq F]

theorem vcFun_add (C : VariableChange F) (W : WeierstrassCurve.Affine F)
    (P Q : (C • W).toAffine.Point) :
    Affine.Point.vcFun C W (P + Q) = Affine.Point.vcFun C W P + Affine.Point.vcFun C W Q := by
  obtain ⟨P', rfl⟩ : ∃ P', P = Affine.Point.vcInvFun C W P' :=
    ⟨Affine.Point.vcFun C W P, (Affine.Point.vcFun_leftInverse P).symm⟩
  obtain ⟨Q', rfl⟩ : ∃ Q', Q = Affine.Point.vcInvFun C W Q' :=
    ⟨Affine.Point.vcFun C W Q, (Affine.Point.vcFun_leftInverse Q).symm⟩
  rw [← Affine.Point.vcInvFun_add, Affine.Point.vcFun_rightInverse, Affine.Point.vcFun_rightInverse,
    Affine.Point.vcFun_rightInverse]

theorem equivOfVariableChangeEq_add {C : VariableChange F} {X Y : WeierstrassCurve.Affine F}
    (h : C • X = Y) (P Q : Y.toAffine.Point) :
    Affine.Point.equivOfVariableChangeEq h (P + Q) =
      Affine.Point.equivOfVariableChangeEq h P + Affine.Point.equivOfVariableChangeEq h Q := by
  subst h; exact vcFun_add C X P Q

noncomputable def eqvHom {C : VariableChange F} {X Y : WeierstrassCurve.Affine F} (h : C • X = Y) :
    Y.toAffine.Point →+ X.toAffine.Point where
  toFun := Affine.Point.equivOfVariableChangeEq h
  map_zero' := by subst h; rfl
  map_add' := equivOfVariableChangeEq_add h

theorem eqvHom_apply {C : VariableChange F} {X Y : WeierstrassCurve.Affine F} (h : C • X = Y)
    (P : Y.toAffine.Point) : eqvHom h P = Affine.Point.equivOfVariableChangeEq h P := rfl

theorem addOrderOf_equivOfVariableChangeEq {C : VariableChange F} {X Y : WeierstrassCurve.Affine F}
    (h : C • X = Y) (P : Y.toAffine.Point) :
    addOrderOf (Affine.Point.equivOfVariableChangeEq h P) = addOrderOf P := by
  rw [← eqvHom_apply]
  exact addOrderOf_injective (eqvHom h) (Affine.Point.equivOfVariableChangeEq h).injective P

theorem nsmul_equivOfVariableChangeEq {C : VariableChange F} {X Y : WeierstrassCurve.Affine F}
    (h : C • X = Y) (P : Y.toAffine.Point) (j : ℕ) :
    j • Affine.Point.equivOfVariableChangeEq h P = Affine.Point.equivOfVariableChangeEq h (j • P) := by
  rw [← eqvHom_apply, ← eqvHom_apply, map_nsmul]

theorem equivOfVariableChangeEq_some {C : VariableChange F} {X Y : WeierstrassCurve.Affine F}
    (h : C • X = Y) (x y : F) (hxy : Y.toAffine.Nonsingular x y) :
    ∃ hxy', Affine.Point.equivOfVariableChangeEq h (.some x y hxy) =
      .some (Affine.vcX C x) (Affine.vcY C x y) hxy' := by
  subst h; exact ⟨_, rfl⟩

theorem equivOfVariableChangeEq_symm_some {C : VariableChange F} {X Y : WeierstrassCurve.Affine F}
    (h : C • X = Y) (x y : F) (hxy : X.toAffine.Nonsingular x y) :
    ∃ hxy', (Affine.Point.equivOfVariableChangeEq h).symm (.some x y hxy) =
      .some (Affine.vcXInv C x) (Affine.vcYInv C x y) hxy' := by
  subst h; exact ⟨_, rfl⟩

theorem coordsOrZero_equivOfVariableChangeEq_one {X Y : WeierstrassCurve.Affine F}
    (h : (1 : VariableChange F) • X = Y) (P : Y.toAffine.Point) :
    (Affine.Point.equivOfVariableChangeEq h P).coordsOrZero = P.coordsOrZero := by
  rcases P with _ | ⟨x, y, hxy⟩
  · show (Affine.Point.equivOfVariableChangeEq h 0).coordsOrZero = (0 : Y.toAffine.Point).coordsOrZero
    rw [← eqvHom_apply, map_zero]
    rfl
  · obtain ⟨hxy', e⟩ := equivOfVariableChangeEq_some h x y hxy
    rw [e, Affine.Point.coordsOrZero_some, Affine.Point.coordsOrZero_some]
    simp only [Affine.vcX, Affine.vcY]
    ext
    · show ((1 : Fˣ) : F) ^ 2 * x + 0 = x
      simp
    · show ((1 : Fˣ) : F) ^ 3 * y + ((1 : Fˣ) : F) ^ 2 * 0 * x + 0 = y
      simp

theorem oddOrderSummingSet_equivOfVariableChangeEq_one {X Y : WeierstrassCurve.Affine F}
    (h : (1 : VariableChange F) • X = Y) (P : Y.toAffine.Point) (n : ℕ) :
    X.oddOrderSummingSet (Affine.Point.equivOfVariableChangeEq h P) n = Y.oddOrderSummingSet P n := by
  simp only [oddOrderSummingSet, nsmul_equivOfVariableChangeEq,
    coordsOrZero_equivOfVariableChangeEq_one]

end VC

section RatPoint

variable {F K : Type} [Field F] [Field K] [DecidableEq F] [DecidableEq K] (f : F →+* K)
  {W : WeierstrassCurve F}

theorem coordsOrZero_ratPointHom (P : W.toAffine.Point) :
    (ratPointHom f P).coordsOrZero = Prod.map f f P.coordsOrZero := by
  rcases P with _ | ⟨x, y, h⟩
  · show (ratPointMap f (0 : W.toAffine.Point)).coordsOrZero = _
    rw [ratPointMap_zero]
    simp [Affine.Point.coordsOrZero]
  · show (ratPointMap f (.some x y h)).coordsOrZero = _
    rw [ratPointMap_some]
    rfl

theorem oddOrderSummingSet_ratPointHom (Q : W.toAffine.Point) (n : ℕ) :
    (W.map f).oddOrderSummingSet (ratPointHom f Q) n =
      (W.oddOrderSummingSet Q n).image (Prod.map f f) := by
  simp only [oddOrderSummingSet, Finset.image_image]
  congr 1
  funext k
  simp only [Function.comp_apply, ← map_nsmul, coordsOrZero_ratPointHom]

end RatPoint

section TwoTorsion

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

omit [DecidableEq F] in
theorem eval_Ψ₂Sq (x : F) :
    W.Ψ₂Sq.eval x = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  simp only [Ψ₂Sq, eval_add, eval_mul, eval_C, eval_pow, eval_X]

omit [DecidableEq F] in

theorem equation_of_eval_Ψ₂Sq_eq_zero (h2 : (2 : F) ≠ 0) {x y : F} (hx : W.Ψ₂Sq.eval x = 0)
    (hy : y * 2 = -(W.a₁ * x + W.a₃)) : W.toAffine.Equation x y := by
  rw [Affine.equation_iff]
  change y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆
  rw [eval_Ψ₂Sq] at hx
  simp only [b₂, b₄, b₆] at hx
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have key : y * 2 + (W.a₁ * x + W.a₃) = 0 := by rw [hy]; ring
  apply mul_left_cancel₀ h4
  linear_combination -1 * hx + (y * 2 + (W.a₁ * x + W.a₃)) * key

omit [DecidableEq F] in
theorem nonsingular_of_eval_Ψ₂Sq_eq_zero [W.IsElliptic] (h2 : (2 : F) ≠ 0) {x y : F}
    (hx : W.Ψ₂Sq.eval x = 0) (hy : y * 2 = -(W.a₁ * x + W.a₃)) : W.toAffine.Nonsingular x y :=
  (Affine.equation_iff_nonsingular).mp (equation_of_eval_Ψ₂Sq_eq_zero W h2 hx hy)

variable {W}

omit [DecidableEq F] in
private theorem some_congr {x₁ y₁ x₂ y₂ : F} (hx : x₁ = x₂)
    (hy : y₁ = y₂) (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

theorem two_smul_eq_zero_of_Y (h2 : (2 : F) ≠ 0) {x y : F} (h : W.toAffine.Nonsingular x y)
    (hy : y * 2 = -(W.a₁ * x + W.a₃)) : (2 : ℤ) • Affine.Point.some x y h = 0 := by
  rw [two_zsmul, add_eq_zero_iff_eq_neg, Affine.Point.neg_some]
  refine some_congr rfl ?_ _ _
  simp only [Affine.negY]
  apply mul_left_cancel₀ h2
  linear_combination 2 * hy

theorem Y_mul_two_of_two_smul_eq_zero {x y : F} (h : W.toAffine.Nonsingular x y)
    (h2P : (2 : ℤ) • Affine.Point.some x y h = 0) : y * 2 = -(W.a₁ * x + W.a₃) := by
  rw [two_zsmul, add_eq_zero_iff_eq_neg, Affine.Point.neg_some, Affine.Point.some.injEq] at h2P
  have hy := h2P.2
  simp only [Affine.negY] at hy
  linear_combination hy

theorem eq_of_fst_eq_of_two_smul_eq_zero {x y y' : F} (h : W.toAffine.Nonsingular x y)
    (h' : W.toAffine.Nonsingular x y') (h2P : (2 : ℤ) • Affine.Point.some x y h = 0) :
    Affine.Point.some x y' h' = Affine.Point.some x y h := by
  by_cases hy : y' = W.toAffine.negY x y
  · have hneg : -Affine.Point.some x y h = Affine.Point.some x y h := by
      rw [two_zsmul, add_eq_zero_iff_eq_neg] at h2P; exact h2P.symm
    rw [← hneg, Affine.Point.neg_some]
    exact some_congr rfl hy _ _
  · have := Affine.Y_eq_of_Y_ne h'.left h.left rfl hy
    subst this
    rfl

omit [DecidableEq F] in

theorem legendreLambda_eq (h2 : (2 : F) ≠ 0) {x₁ x₂ : F} (hx : x₁ ≠ x₂) :
    W.legendreLambda x₁ x₂ = (-W.b₂ - 8 * x₁ - 4 * x₂) / (4 * (x₂ - x₁)) := by
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hx' : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  rw [legendreLambda_def]
  field_simp
  ring

end TwoTorsion

theorem equation_of_mem_oddOrderSummingSet {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) (Q : W.toAffine.Point) (n : ℕ) (hQ : addOrderOf Q = 2 * n + 1)
    {P : F × F} (hP : P ∈ W.oddOrderSummingSet Q n) : W.toAffine.Equation P.1 P.2 := by
  rw [mem_oddOrderSummingSet] at hP
  obtain ⟨k, hk1, hkn, rfl⟩ := hP
  have hk0 : k • Q ≠ 0 := nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)
  rcases hkQ : k • Q with _ | ⟨x, y, h⟩
  · exact absurd hkQ hk0
  · exact h.1

section Witt

variable (p : ℕ) [Fact p.Prime] (k : Type*) [CommRing k] [CharP k p] [Nontrivial k]

theorem charZero_wittVector : CharZero (WittVector p k) := by
  have hinj : Function.Injective (WittVector.map (p := p) (ZMod.castHom (dvd_refl p) k)) :=
    WittVector.map_injective _ (ZMod.castHom (dvd_refl p) k).injective
  haveI : CharZero (WittVector p (ZMod p)) :=
    (WittVector.equiv p).toRingHom.charZero
  refine ⟨fun a b hab => ?_⟩
  have h : WittVector.map (p := p) (ZMod.castHom (dvd_refl p) k) (a : WittVector p (ZMod p)) =
      WittVector.map (p := p) (ZMod.castHom (dvd_refl p) k) (b : WittVector p (ZMod p)) := by
    rw [map_natCast, map_natCast]; exact hab
  exact Nat.cast_injective (hinj h)

end Witt

open scoped Classical in

theorem specialise {𝒪 : Type} [CommRing 𝒪] {k : Type} [Field k] [DecidableEq k]
    (π : 𝒪 →+* k) (h2 : (2 : k) ≠ 0)
    (E : WeierstrassCurve (PowerSeries 𝒪)) [E.IsElliptic] (n : ℕ) (hm : ((2 * n + 1 : ℕ) : k) ≠ 0)
    (Q₀ : (E.map (π.comp (PowerSeries.constantCoeff (R := 𝒪)))).toAffine.Point)
    (hQ₀ : addOrderOf Q₀ = 2 * n + 1)
    {h : Polynomial (PowerSeries 𝒪)} (hh : h.Monic) (hdvd : h ∣ E.preΨ' (2 * n + 1))
    (hmap : h.map (π.comp (PowerSeries.constantCoeff (R := 𝒪))) =
      kernelPolynomial ((E.map (π.comp (PowerSeries.constantCoeff (R := 𝒪)))).oddOrderSummingSet Q₀ n))
    [(E.kohelQuotient h).IsElliptic]
    {x₁ y₁ x₂ y₂ x'₁ x'₂ : k}
    (h₁ : (E.map (π.comp (PowerSeries.constantCoeff (R := 𝒪)))).toAffine.Nonsingular x₁ y₁)
    (h₂ : (E.map (π.comp (PowerSeries.constantCoeff (R := 𝒪)))).toAffine.Nonsingular x₂ y₂)
    (hP₁ : (2 : ℤ) • (Affine.Point.some x₁ y₁ h₁) = 0)
    (hP₂ : (2 : ℤ) • (Affine.Point.some x₂ y₂ h₂) = 0)
    (hx : x₁ ≠ x₂) (hx' : x'₁ ≠ x'₂)
    {e₁ e₂ e'₁ e'₂ : PowerSeries 𝒪}
    (he₁ : E.Ψ₂Sq.eval e₁ = 0) (he₂ : E.Ψ₂Sq.eval e₂ = 0)
    (he'₁ : (E.kohelQuotient h).Ψ₂Sq.eval e'₁ = 0) (he'₂ : (E.kohelQuotient h).Ψ₂Sq.eval e'₂ = 0)
    (he₁₀ : π (PowerSeries.constantCoeff e₁) = x₁) (he₂₀ : π (PowerSeries.constantCoeff e₂) = x₂)
    (he'₁₀ : π (PowerSeries.constantCoeff e'₁) = x'₁) (he'₂₀ : π (PowerSeries.constantCoeff e'₂) = x'₂)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (V : ValuationSubring Ω)
    [HenselianLocalRing V] [IsAlgClosed (ResidueField V)] (φ : k ≃+* ResidueField V)
    (φsp : PowerSeries 𝒪 →+* V)
    (hcomp : (residue V).comp φsp = φ.toRingHom.comp (π.comp (PowerSeries.constantCoeff (R := 𝒪))))
    (hφF : φsp ((-E.b₂ - 8 * e₁ - 4 * e₂) * (e'₂ - e'₁)
      - (-(E.kohelQuotient h).b₂ - 8 * e'₁ - 4 * e'₂) * (e₂ - e₁)) = 0) :
    ∃ (hΔ' : ((E.map φsp).map (residue V)).Δ ≠ 0)
      (hv' : (1 : VariableChange (ResidueField V)) • (E.map φsp).map (residue V) =
        (E.map (π.comp (PowerSeries.constantCoeff (R := 𝒪)))).map φ.toRingHom)
      (Q' : ((E.map φsp).map V.subtype).toAffine.Point) (_ : addOrderOf Q' = 2 * n + 1)
      (_ : ratPointHom φ.toRingHom Q₀ =
        (Affine.Point.equivOfVariableChangeEq hv').symm (reduceHom hΔ' Q'))
      (γ : VariableChange Ω)
      (hγ : γ • (E.map φsp).map V.subtype =
        ((E.map φsp).map V.subtype).veluQuotient
          (((E.map φsp).map V.subtype).oddOrderSummingSet Q' n))
      (t₁ t₂ : Ω)
      (hT₁ : ((E.map φsp).map V.subtype).toAffine.Nonsingular (φsp e₁) t₁)
      (hT₂ : ((E.map φsp).map V.subtype).toAffine.Nonsingular (φsp e₂) t₂)
      (t'₁ t'₂ : Ω)
      (hT'₁ : (((E.map φsp).map V.subtype).veluQuotient
        (((E.map φsp).map V.subtype).oddOrderSummingSet Q' n)).toAffine.Nonsingular (φsp e'₁) t'₁)
      (hT'₂ : (((E.map φsp).map V.subtype).veluQuotient
        (((E.map φsp).map V.subtype).oddOrderSummingSet Q' n)).toAffine.Nonsingular (φsp e'₂) t'₂),
      (2 : ℤ) • Affine.Point.some _ _ hT₁ = 0 ∧ (2 : ℤ) • Affine.Point.some _ _ hT₂ = 0 ∧
      ratPointHom φ.toRingHom (.some x₁ y₁ h₁) =
        (Affine.Point.equivOfVariableChangeEq hv').symm (reduceHom hΔ' (.some _ _ hT₁)) ∧
      ratPointHom φ.toRingHom (.some x₂ y₂ h₂) =
        (Affine.Point.equivOfVariableChangeEq hv').symm (reduceHom hΔ' (.some _ _ hT₂)) ∧
      Affine.Point.equivOfVariableChangeEq hγ (.some _ _ hT'₁) = .some _ _ hT₁ ∧
      Affine.Point.equivOfVariableChangeEq hγ (.some _ _ hT'₂) = .some _ _ hT₂ ∧
      residue V (φsp e'₁) = φ x'₁ ∧ residue V (φsp e'₂) = φ x'₂ := by
  classical
  set E₁ : WeierstrassCurve (PowerSeries 𝒪) := E.kohelQuotient h with hE₁_def
  have hcomp' : ∀ G, residue V (φsp G) = φ (π (PowerSeries.constantCoeff G)) := fun G => by
    have := RingHom.congr_fun hcomp G
    simpa using this

  set E' : WeierstrassCurve V := E.map φsp with hE'_def
  have hΔ' : (E'.map (residue V)).Δ ≠ 0 := by
    rw [map_Δ, hE'_def, map_Δ, residue_ne_zero_iff_isUnit]
    exact (E.isUnit_Δ).map φsp
  have hv' : (1 : VariableChange (ResidueField V)) • E'.map (residue V) =
      (E.map (π.comp (PowerSeries.constantCoeff (R := 𝒪)))).map φ.toRingHom := by
    rw [one_smul, hE'_def, map_map, hcomp, ← map_map]

  set EΩ : WeierstrassCurve Ω := E'.map V.subtype with hEΩ_def
  set φΩ : PowerSeries 𝒪 →+* Ω := V.subtype.comp φsp with hφΩ_def
  have hEΩ : EΩ = E.map φΩ := by rw [hEΩ_def, hE'_def, map_map]
  haveI hEΩell : EΩ.IsElliptic := by rw [hEΩ_def]; infer_instance
  have h2V : (2 : ResidueField V) ≠ 0 := by
    rw [← map_ofNat φ 2]; exact (map_ne_zero φ).mpr h2
  have hmV : ((2 * n + 1 : ℕ) : ResidueField V) ≠ 0 := by
    rw [← map_natCast φ]; exact (map_ne_zero φ).mpr hm

  set Q₀' : (E'.map (residue V)).toAffine.Point :=
    Affine.Point.equivOfVariableChangeEq hv' (ratPointHom φ.toRingHom Q₀) with hQ₀'_def
  have hQ₀' : addOrderOf Q₀' = 2 * n + 1 := by
    rw [hQ₀'_def, addOrderOf_equivOfVariableChangeEq]
    exact (addOrderOf_injective (ratPointHom φ.toRingHom)
      (fun a b hab => ratPointMap_injective φ.toRingHom hab) Q₀).trans hQ₀
  have hmap' : (h.map φsp).map (residue V) =
      kernelPolynomial ((E'.map (residue V)).oddOrderSummingSet Q₀' n) := by
    rw [hQ₀'_def, oddOrderSummingSet_equivOfVariableChangeEq_one, oddOrderSummingSet_ratPointHom,
      ← map_kernelPolynomial_of_injOn φ.toRingHom _
        ((φ.injective.prodMap φ.injective).injOn),
      ← hmap, Polynomial.map_map, Polynomial.map_map, hcomp]
  have hdvd' : h.map φsp ∣ E'.preΨ' (2 * n + 1) := by
    rw [hE'_def, map_preΨ']; exact Polynomial.map_dvd φsp hdvd
  obtain ⟨Q', hQ'ord, hQ'red, hQ'ker⟩ :=
    exists_reduceHom_eq_and_map_eq_kernelPolynomial_oddOrderSummingSet hΔ' hmV Q₀' hQ₀'
      (hh.map φsp) hdvd' hmap'
  set S' := EΩ.oddOrderSummingSet Q' n with hS'_def

  have hE₁Ω : E₁.map φΩ = EΩ.veluQuotient S' := by
    rw [hE₁_def, map_kohelQuotient E φΩ hh, hφΩ_def, ← Polynomial.map_map, hQ'ker, ← hφΩ_def,
      ← hEΩ]
    exact kohelQuotient_kernelPolynomial_eq_veluQuotient EΩ S'
      (fun P hP => equation_of_mem_oddOrderSummingSet EΩ Q' n hQ'ord hP)
  haveI hE₁Ωell : (E₁.map φΩ).IsElliptic := inferInstance
  have h2Ω : (2 : Ω) ≠ 0 := two_ne_zero
  have h4Ω : (4 : Ω) ≠ 0 := by norm_num

  set f₁ : V := φsp e₁ with hf₁
  set f₂ : V := φsp e₂ with hf₂
  set f'₁ : V := φsp e'₁ with hf'₁
  set f'₂ : V := φsp e'₂ with hf'₂
  have hres : ∀ {e : PowerSeries 𝒪} {x : k}, π (PowerSeries.constantCoeff e) = x →
      residue V (φsp e) = φ x := fun {e x} hex => by rw [hcomp' e]; exact congrArg φ hex
  have hne : (f₁ : Ω) ≠ f₂ := by
    intro h12
    apply hx
    have h12' : f₁ = f₂ := Subtype.ext h12
    have := congrArg (residue V) h12'
    rw [hf₁, hf₂, hres he₁₀, hres he₂₀] at this
    exact φ.injective this
  have hne' : (f'₁ : Ω) ≠ f'₂ := by
    intro h12
    apply hx'
    have h12' : f'₁ = f'₂ := Subtype.ext h12
    have := congrArg (residue V) h12'
    rw [hf'₁, hf'₂, hres he'₁₀, hres he'₂₀] at this
    exact φ.injective this

  have hrootΩ : ∀ (X : WeierstrassCurve (PowerSeries 𝒪)) {e : PowerSeries 𝒪},
      X.Ψ₂Sq.eval e = 0 → (X.map φΩ).Ψ₂Sq.eval (φΩ e) = 0 := by
    intro X e hXe
    rw [map_Ψ₂Sq, eval_map, eval₂_hom, hXe, map_zero]
  have hf₁root : EΩ.Ψ₂Sq.eval (f₁ : Ω) = 0 := by rw [hEΩ]; exact hrootΩ E he₁
  have hf₂root : EΩ.Ψ₂Sq.eval (f₂ : Ω) = 0 := by rw [hEΩ]; exact hrootΩ E he₂
  have hf'₁root : (EΩ.veluQuotient S').Ψ₂Sq.eval (f'₁ : Ω) = 0 := by
    rw [← hE₁Ω]; exact hrootΩ E₁ he'₁
  have hf'₂root : (EΩ.veluQuotient S').Ψ₂Sq.eval (f'₂ : Ω) = 0 := by
    rw [← hE₁Ω]; exact hrootΩ E₁ he'₂

  set t₁ : Ω := -(EΩ.a₁ * f₁ + EΩ.a₃) / 2 with ht₁
  set t₂ : Ω := -(EΩ.a₁ * f₂ + EΩ.a₃) / 2 with ht₂
  set t'₁ : Ω := -((EΩ.veluQuotient S').a₁ * f'₁ + (EΩ.veluQuotient S').a₃) / 2 with ht'₁
  set t'₂ : Ω := -((EΩ.veluQuotient S').a₁ * f'₂ + (EΩ.veluQuotient S').a₃) / 2 with ht'₂
  have hty : ∀ (X : WeierstrassCurve Ω) (x : Ω),
      -(X.a₁ * x + X.a₃) / 2 * 2 = -(X.a₁ * x + X.a₃) := fun X x => div_mul_cancel₀ _ h2Ω
  have hT₁ : EΩ.toAffine.Nonsingular f₁ t₁ :=
    nonsingular_of_eval_Ψ₂Sq_eq_zero EΩ h2Ω hf₁root (hty _ _)
  have hT₂ : EΩ.toAffine.Nonsingular f₂ t₂ :=
    nonsingular_of_eval_Ψ₂Sq_eq_zero EΩ h2Ω hf₂root (hty _ _)
  have hquotell : (EΩ.veluQuotient S').IsElliptic := by rw [← hE₁Ω]; infer_instance
  have hT'₁ : (EΩ.veluQuotient S').toAffine.Nonsingular f'₁ t'₁ :=
    @nonsingular_of_eval_Ψ₂Sq_eq_zero _ _ (EΩ.veluQuotient S') hquotell h2Ω _ _ hf'₁root (hty _ _)
  have hT'₂ : (EΩ.veluQuotient S').toAffine.Nonsingular f'₂ t'₂ :=
    @nonsingular_of_eval_Ψ₂Sq_eq_zero _ _ (EΩ.veluQuotient S') hquotell h2Ω _ _ hf'₂root (hty _ _)
  have h2T₁ := two_smul_eq_zero_of_Y h2Ω hT₁ (hty _ _)
  have h2T₂ := two_smul_eq_zero_of_Y h2Ω hT₂ (hty _ _)
  have h2T'₁ := two_smul_eq_zero_of_Y h2Ω hT'₁ (hty _ _)
  have h2T'₂ := two_smul_eq_zero_of_Y h2Ω hT'₂ (hty _ _)

  have hlam : EΩ.legendreLambda f₁ f₂ = (EΩ.veluQuotient S').legendreLambda f'₁ f'₂ := by
    rw [legendreLambda_eq (W := EΩ) h2Ω hne, legendreLambda_eq (W := EΩ.veluQuotient S') h2Ω hne',
      div_eq_div_iff (mul_ne_zero h4Ω (sub_ne_zero.mpr (Ne.symm hne)))
        (mul_ne_zero h4Ω (sub_ne_zero.mpr (Ne.symm hne'))),
      ← hE₁Ω, hEΩ, map_b₂, map_b₂]
    have key : φΩ ((-E.b₂ - 8 * e₁ - 4 * e₂) * (e'₂ - e'₁)
      - (-E₁.b₂ - 8 * e'₁ - 4 * e'₂) * (e₂ - e₁)) = 0 := by
      rw [hφΩ_def, RingHom.comp_apply, hE₁_def, hφF, map_zero]
    simp only [map_sub, map_mul, map_neg, map_ofNat] at key
    have ef₁ : φΩ e₁ = f₁ := rfl
    have ef₂ : φΩ e₂ = f₂ := rfl
    have ef'₁ : φΩ e'₁ = f'₁ := rfl
    have ef'₂ : φΩ e'₂ = f'₂ := rfl
    rw [ef₁, ef₂, ef'₁, ef'₂] at key
    linear_combination 4 * key
  obtain ⟨u, hu⟩ : ∃ u : Ω, u ^ 2 * ((f'₂ : Ω) - f'₁) = (f₂ : Ω) - f₁ := by
    obtain ⟨z, hz⟩ :=
      IsAlgClosed.exists_pow_nat_eq (((f₂ : Ω) - f₁) / ((f'₂ : Ω) - f'₁)) two_pos
    exact ⟨z, by rw [hz, div_mul_cancel₀ _ (sub_ne_zero.mpr (Ne.symm hne'))]⟩
  obtain ⟨γ, hγ, hγ₁, hγ₂⟩ :=
    exists_variableChange_of_legendreLambda_eq h2Ω EΩ (EΩ.veluQuotient S') hT₁ hT₂ h2T₁ h2T₂ hne
      hT'₁ hT'₂ h2T'₁ h2T'₂ hne' hu hlam

  have hred : ∀ {x y : k}
      (hxy : (E.map (π.comp (PowerSeries.constantCoeff (R := 𝒪)))).toAffine.Nonsingular x y)
      (h2P : (2 : ℤ) • Affine.Point.some x y hxy = 0) {f : V} {t : Ω}
      (hT : EΩ.toAffine.Nonsingular f t) (hf : residue V f = φ x),
      ratPointHom φ.toRingHom (.some x y hxy) =
        (Affine.Point.equivOfVariableChangeEq hv').symm (reduceHom hΔ' (.some _ _ hT)) := by
    intro x y hxy h2P f t hT hf

    have hfmem : (f : Ω) ∈ V := f.2
    have hred1 : reduceHom hΔ' (.some (f : Ω) t hT) = reducePoint hΔ' (.some (f : Ω) t hT) := rfl
    rw [hred1, reducePoint_some_of_mem hΔ' hT hfmem]
    obtain ⟨hxy', e⟩ := equivOfVariableChangeEq_symm_some hv'
      (residue V ⟨(f : Ω), hfmem⟩) (residue V ⟨t, Affine.Y_mem_of_X_mem E' hT.1 hfmem⟩)
      (Affine.nonsingular_residue E' hΔ' hT.1)
    rw [e]

    have hxeq : φ x =
        Affine.vcXInv (1 : VariableChange (ResidueField V)) (residue V ⟨(f : Ω), hfmem⟩) := by
      have hff : (⟨(f : Ω), hfmem⟩ : V) = f := Subtype.ext rfl
      rw [hff, hf]
      show φ x = (((1 : (ResidueField V)ˣ)⁻¹ : (ResidueField V)ˣ) : ResidueField V) ^ 2 * (φ x - 0)
      simp
    have hL : ratPointHom φ.toRingHom (.some x y hxy) =
        .some (φ x) (φ y) (((E.map (π.comp (PowerSeries.constantCoeff (R := 𝒪)))).toAffine.map_nonsingular
          φ.toRingHom.injective x y).mpr hxy) :=
      rfl
    have h2L : (2 : ℤ) • ratPointHom φ.toRingHom (.some x y hxy) = 0 := by
      rw [← map_zsmul, h2P, map_zero]
    rw [hL] at h2L ⊢
    clear e
    symm
    revert hxy'
    rw [← hxeq]
    intro hxy'
    exact eq_of_fst_eq_of_two_smul_eq_zero _ _ h2L
  have hR₁ := hred h₁ hP₁ hT₁ (hres he₁₀)
  have hR₂ := hred h₂ hP₂ hT₂ (hres he₂₀)
  have hRQ : ratPointHom φ.toRingHom Q₀ =
      (Affine.Point.equivOfVariableChangeEq hv').symm (reduceHom hΔ' Q') := by
    rw [Equiv.eq_symm_apply, hQ'red]

  exact ⟨hΔ', hv', Q', hQ'ord, hRQ, γ, hγ, t₁, t₂, hT₁, hT₂, t'₁, t'₂, hT'₁, hT'₂, h2T₁, h2T₂,
    hR₁, hR₂, hγ₁, hγ₂, hres he'₁₀, hres he'₂₀⟩

open scoped Classical in
theorem main (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p] [DecidableEq k]
    (h2 : (2 : k) ≠ 0)
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (hm : ((2 * n + 1 : ℕ) : k) ≠ 0)
    (hsq : ¬ IsSquare (2 * n + 1)) (Q₀ : W.toAffine.Point) (hQ₀ : addOrderOf Q₀ = 2 * n + 1)
    (γ₀ : VariableChange k)
    (hγ₀ : γ₀ • W = W.veluQuotient (W.oddOrderSummingSet Q₀ n))
    {x₁ y₁ x₂ y₂ : k} (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hP₁ : (2 : ℤ) • (Affine.Point.some x₁ y₁ h₁) = 0)
    (hP₂ : (2 : ℤ) • (Affine.Point.some x₂ y₂ h₂) = 0)
    (hx : x₁ ≠ x₂)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    [Algebra (FractionRing (WittVector p k)) Ω]
    [Algebra.IsAlgebraic (FractionRing (WittVector p k)) Ω] :
    ∃ (B : ValuationSubring Ω) (φ : k ≃+* ResidueField B)
      (E' : WeierstrassCurve B)
      (_ : E'.IsElliptic) (hΔ' : (E'.map (residue B)).Δ ≠ 0)
      (hv' : (1 : VariableChange (ResidueField B)) • E'.map (residue B) = W.map φ.toRingHom)
      (Q' : (E'.map B.subtype).toAffine.Point) (_ : addOrderOf Q' = 2 * n + 1)
      (_ : ratPointHom φ.toRingHom Q₀ =
        (Affine.Point.equivOfVariableChangeEq hv').symm (reduceHom hΔ' Q'))
      (γ : VariableChange Ω)
      (hγ : γ • E'.map B.subtype =
        (E'.map B.subtype).veluQuotient ((E'.map B.subtype).oddOrderSummingSet Q' n))
      (e₁ e₂ : B) (t₁ t₂ : Ω)
      (hT₁ : (E'.map B.subtype).toAffine.Nonsingular e₁ t₁)
      (hT₂ : (E'.map B.subtype).toAffine.Nonsingular e₂ t₂)
      (e'₁ e'₂ : B) (t'₁ t'₂ : Ω)
      (hT'₁ : ((E'.map B.subtype).veluQuotient
        ((E'.map B.subtype).oddOrderSummingSet Q' n)).toAffine.Nonsingular e'₁ t'₁)
      (hT'₂ : ((E'.map B.subtype).veluQuotient
        ((E'.map B.subtype).oddOrderSummingSet Q' n)).toAffine.Nonsingular e'₂ t'₂),
      (2 : ℤ) • Affine.Point.some _ _ hT₁ = 0 ∧ (2 : ℤ) • Affine.Point.some _ _ hT₂ = 0 ∧
      ratPointHom φ.toRingHom (.some x₁ y₁ h₁) =
        (Affine.Point.equivOfVariableChangeEq hv').symm (reduceHom hΔ' (.some _ _ hT₁)) ∧
      ratPointHom φ.toRingHom (.some x₂ y₂ h₂) =
        (Affine.Point.equivOfVariableChangeEq hv').symm (reduceHom hΔ' (.some _ _ hT₂)) ∧
      Affine.Point.equivOfVariableChangeEq hγ (.some _ _ hT'₁) = .some _ _ hT₁ ∧
      Affine.Point.equivOfVariableChangeEq hγ (.some _ _ hT'₂) = .some _ _ hT₂ ∧
      residue B e'₁ = φ (Affine.vcXInv γ₀ x₁) ∧ residue B e'₂ = φ (Affine.vcXInv γ₀ x₂) := by
  classical

  haveI : CharZero (WittVector p k) := charZero_wittVector p k
  let π : WittVector p k →+* k := WittVector.constantCoeff
  have hπ : Function.Surjective π := WittVector.constantCoeff_surjective p
  have hkerπ : RingHom.ker π = Ideal.span {(p : WittVector p k)} := WittVector.ker_constantCoeff
  haveI : IsAdicComplete (RingHom.ker π) (WittVector p k) := by rw [hkerπ]; infer_instance
  have hmax : maximalIdeal (WittVector p k) = RingHom.ker π := by
    rw [hkerπ]
    exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp
      (WittVector.irreducible (p := p))
  haveI : IsAdicComplete (maximalIdeal (WittVector p k)) (WittVector p k) := by
    rw [hmax]; infer_instance

  letI : Algebra (WittVector p k) Ω :=
    ((algebraMap (FractionRing (WittVector p k)) Ω).comp
      (algebraMap (WittVector p k) (FractionRing (WittVector p k)))).toAlgebra
  haveI : IsScalarTower (WittVector p k) (FractionRing (WittVector p k)) Ω :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have halg_inj : Function.Injective (algebraMap (WittVector p k) Ω) :=
    (algebraMap (FractionRing (WittVector p k)) Ω).injective.comp
      (IsFractionRing.injective (WittVector p k) (FractionRing (WittVector p k)))
  haveI : FaithfulSMul (WittVector p k) Ω :=
    (faithfulSMul_iff_algebraMap_injective (WittVector p k) Ω).mpr halg_inj
  haveI : Algebra.IsAlgebraic (WittVector p k) Ω :=
    (IsFractionRing.comap_isAlgebraic_iff (K := FractionRing (WittVector p k))).mpr inferInstance
  obtain ⟨V, hV, φ, hdom, hφ⟩ :=
    WittVector.exists_valuationSubring_residueField_equiv_of_isAlgebraic p k Ω
  haveI : HenselianLocalRing V := ValuationSubring.henselianLocalRing_of_isAlgClosed V
  haveI : IsAlgClosed (ResidueField V) := ValuationSubring.isAlgClosed_residueField V

  obtain ⟨E, hEell, hEW, hj, h, hh, hdvd, hmap, hE₁ell, e₁, e₂, e'₁, e'₂, he₁, he₂, he'₁, he'₂,
      he₁₀, he₂₀, he'₁₀, he'₂₀, hF0, hF⟩ :=
    exists_powerSeries_deformation_kohelQuotient_twoTorsion_legendreCross_of_smul_eq_veluQuotient
      π hπ h2 W n hm hsq Q₀ hQ₀ γ₀ hγ₀ h₁ h₂ hP₁ hP₂ hx
  subst hEW
  obtain ⟨FL, hFL_def⟩ : ∃ FL : PowerSeries (WittVector p k), FL =
      (-E.b₂ - 8 * e₁ - 4 * e₂) * (e'₂ - e'₁)
        - (-(E.kohelQuotient h).b₂ - 8 * e'₁ - 4 * e'₂) * (e₂ - e₁) := ⟨_, rfl⟩
  rw [← hFL_def] at hF0 hF

  have hFL0 : PowerSeries.constantCoeff FL ∈ maximalIdeal (WittVector p k) := by
    rw [hmax, RingHom.mem_ker]; exact hF0
  have hFL : PowerSeries.map (residue (WittVector p k)) FL ≠ 0 := by
    intro h0
    apply hF
    have hker : RingHom.ker (residue (WittVector p k)) ≤ RingHom.ker π := by
      rw [ker_residue, hmax]
    have hsurj : Function.Surjective (residue (WittVector p k)) := residue_surjective
    obtain ⟨ψ, hψ⟩ : ∃ ψ : ResidueField (WittVector p k) →+* k, ψ.comp (residue _) = π :=
      ⟨(residue (WittVector p k)).liftOfRightInverse (Function.surjInv hsurj)
          (Function.rightInverse_surjInv hsurj) ⟨π, hker⟩,
        RingHom.ext fun x => (residue (WittVector p k)).liftOfRightInverse_comp_apply
          (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj) ⟨π, hker⟩ x⟩
    rw [← hψ, PowerSeries.map_comp, RingHom.comp_apply, h0, map_zero]
  obtain ⟨φsp, hφC, -, -, hφres, -, -, hφF⟩ :=
    PowerSeries.exists_ringHom_valuationSubring_map_eq_zero_of_constantCoeff_mem_maximalIdeal
      FL hFL0 hFL V hV hdom

  have hcomp : (residue V).comp φsp =
      φ.toRingHom.comp (π.comp (PowerSeries.constantCoeff (R := WittVector p k))) := by
    ext G
    rw [RingHom.comp_apply, RingHom.comp_apply, hφres G, RingHom.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    have e1 : φsp (PowerSeries.C (PowerSeries.constantCoeff G)) =
        ⟨algebraMap (WittVector p k) Ω (PowerSeries.constantCoeff G), hV _⟩ := Subtype.ext (hφC _)
    rw [e1, ← hφ]
    rfl
  rw [hFL_def] at hφF

  have hx' : Affine.vcXInv γ₀ x₁ ≠ Affine.vcXInv γ₀ x₂ := by
    intro h12
    apply hx
    rw [← Affine.vcX_vcXInv (C := γ₀) x₁, ← Affine.vcX_vcXInv (C := γ₀) x₂]
    exact congrArg _ h12
  obtain ⟨hΔ', hv', Q', hQ'ord, hRQ, γ, hγ, t₁, t₂, hT₁, hT₂, t'₁, t'₂, hT'₁, hT'₂, h2T₁, h2T₂,
      hR₁, hR₂, hγ₁, hγ₂, hr₁, hr₂⟩ :=
    specialise π h2 E n hm Q₀ hQ₀ hh hdvd hmap h₁ h₂ hP₁ hP₂ hx hx' he₁ he₂ he'₁ he'₂
      he₁₀ he₂₀ he'₁₀ he'₂₀ V φ φsp hcomp hφF
  exact ⟨V, φ, E.map φsp, inferInstance, hΔ', hv', Q', hQ'ord, hRQ, γ, hγ, φsp e₁, φsp e₂, t₁, t₂,
    hT₁, hT₂, φsp e'₁, φsp e'₂, t'₁, t'₂, hT'₁, hT'₂, h2T₁, h2T₂, hR₁, hR₂, hγ₁, hγ₂, hr₁, hr₂⟩

end DeuringMarkedLift

end WeierstrassCurve

open scoped Classical in

theorem solution
    (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p] [DecidableEq k]
    (h2 : (2 : k) ≠ 0)
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (hm : ((2 * n + 1 : ℕ) : k) ≠ 0)
    (hsq : ¬ IsSquare (2 * n + 1)) (Q₀ : W.toAffine.Point) (hQ₀ : addOrderOf Q₀ = 2 * n + 1)
    (γ₀ : WeierstrassCurve.VariableChange k)
    (hγ₀ : γ₀ • W = W.veluQuotient (W.oddOrderSummingSet Q₀ n))
    {x₁ y₁ x₂ y₂ : k} (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hP₁ : (2 : ℤ) • (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) = 0)
    (hP₂ : (2 : ℤ) • (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) = 0)
    (hx : x₁ ≠ x₂)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    [Algebra (FractionRing (WittVector p k)) Ω]
    [Algebra.IsAlgebraic (FractionRing (WittVector p k)) Ω] :
    ∃ (B : ValuationSubring Ω) (φ : k ≃+* IsLocalRing.ResidueField B)
      (E' : WeierstrassCurve B)
      (_ : E'.IsElliptic) (hΔ' : (E'.map (IsLocalRing.residue B)).Δ ≠ 0)
      (hv' : (1 : WeierstrassCurve.VariableChange (IsLocalRing.ResidueField B)) •
        E'.map (IsLocalRing.residue B) = W.map φ.toRingHom)
      (Q' : (E'.map B.subtype).toAffine.Point) (_ : addOrderOf Q' = 2 * n + 1)
      (_ : WeierstrassCurve.ratPointHom φ.toRingHom Q₀ =
        (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv').symm
          (WeierstrassCurve.reduceHom hΔ' Q'))
      (γ : WeierstrassCurve.VariableChange Ω)
      (hγ : γ • E'.map B.subtype =
        (E'.map B.subtype).veluQuotient ((E'.map B.subtype).oddOrderSummingSet Q' n))
      (e₁ e₂ : B) (t₁ t₂ : Ω)
      (hT₁ : (E'.map B.subtype).toAffine.Nonsingular e₁ t₁)
      (hT₂ : (E'.map B.subtype).toAffine.Nonsingular e₂ t₂)
      (e'₁ e'₂ : B) (t'₁ t'₂ : Ω)
      (hT'₁ : ((E'.map B.subtype).veluQuotient
        ((E'.map B.subtype).oddOrderSummingSet Q' n)).toAffine.Nonsingular e'₁ t'₁)
      (hT'₂ : ((E'.map B.subtype).veluQuotient
        ((E'.map B.subtype).oddOrderSummingSet Q' n)).toAffine.Nonsingular e'₂ t'₂),
      (2 : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hT₁ = 0 ∧
      (2 : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hT₂ = 0 ∧
      WeierstrassCurve.ratPointHom φ.toRingHom (.some x₁ y₁ h₁) =
        (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv').symm
          (WeierstrassCurve.reduceHom hΔ' (.some _ _ hT₁)) ∧
      WeierstrassCurve.ratPointHom φ.toRingHom (.some x₂ y₂ h₂) =
        (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv').symm
          (WeierstrassCurve.reduceHom hΔ' (.some _ _ hT₂)) ∧
      WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hγ (.some _ _ hT'₁) = .some _ _ hT₁ ∧
      WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hγ (.some _ _ hT'₂) = .some _ _ hT₂ ∧
      IsLocalRing.residue B e'₁ = φ (WeierstrassCurve.Affine.vcXInv γ₀ x₁) ∧
      IsLocalRing.residue B e'₂ = φ (WeierstrassCurve.Affine.vcXInv γ₀ x₂) :=
  WeierstrassCurve.DeuringMarkedLift.main p h2 W n hm hsq Q₀ hQ₀ γ₀ hγ₀ h₁ h₂ hP₁ hP₂ hx Ω

end S_WeierstrassCurve_exists_valuationSubring_lift_variableChange_veluQuotient_apply_twoTorsion_eq_of_smul_eq_veluQuotient
end P2MW
export P2MW.S_WeierstrassCurve_exists_valuationSubring_lift_variableChange_veluQuotient_apply_twoTorsion_eq_of_smul_eq_veluQuotient (solution)
