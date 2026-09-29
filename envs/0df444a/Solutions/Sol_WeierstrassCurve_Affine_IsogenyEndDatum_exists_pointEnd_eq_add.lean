-- Prove2me | solution 1 for WeierstrassCurve.Affine.IsogenyEndDatum.exists_pointEnd_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/a24dbee0-0d9f-543d-87f2-417d05609f01

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Theorems.Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_restrictAlong_placeOfPoint_eq_add
import Theorems.Thm_WeierstrassCurve_Affine_IsogenyEndDatum_pointEnd_apply_eq_sub
import Theorems.Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField
import Theorems.Thm_AlgebraicCurve_normFormulaAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_pointEnd_eq_add
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply"
p2m_attr_erase "simp" "ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u

theorem normFormulaAlong_of_finiteAlong_aux
    {F : Type u} [Field F] [CharZero F] {V W : WeierstrassCurve.Affine F}
    [HasPrincipalDivisors F W.FunctionField]
    (ι : V.FunctionField →ₐ[F] W.FunctionField) (hfin : FiniteAlong F ι) :
    NormFormulaAlong F ι hfin := by
  haveI : CharZero V.FunctionField :=
    charZero_of_injective_algebraMap (algebraMap F V.FunctionField).injective
  have hsep : SeparableAlong F ι := by
    letI := algebraAlong ι
    haveI := isScalarTower_along ι
    haveI : Module.Finite V.FunctionField W.FunctionField := hfin
    show Algebra.IsSeparable V.FunctionField W.FunctionField
    infer_instance
  exact AlgebraicCurve.normFormulaAlong ι hfin hsep

theorem solution
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {W : WeierstrassCurve.Affine F} [W.IsElliptic]
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [AbelTheorem W]
    (D₁ : IsogenyEndDatum W) (hN₁ : NormFormulaAlong F D₁.ι D₁.hfin)
    (D₂ : IsogenyEndDatum W) (hN₂ : NormFormulaAlong F D₂.ι D₂.hfin)
    (h : D₁.pointEnd hN₁ + D₂.pointEnd hN₂ ≠ 0) :
    ∃ (D₃ : IsogenyEndDatum W) (hN₃ : NormFormulaAlong F D₃.ι D₃.hfin),
      D₃.pointEnd hN₃ = D₁.pointEnd hN₁ + D₂.pointEnd hN₂ := by

  obtain ⟨D₃, hD₃⟩ :=
    IsogenyEndDatum.exists_restrictAlong_placeOfPoint_eq_add D₁ hN₁ D₂ hN₂ h

  haveI : HasPrincipalDivisors F W.FunctionField := hasPrincipalDivisors_functionField W
  have hN₃ : NormFormulaAlong F D₃.ι D₃.hfin := normFormulaAlong_of_finiteAlong_aux D₃.ι D₃.hfin
  refine ⟨D₃, hN₃, ?_⟩

  refine AddMonoidHom.ext fun P => ?_
  show D₃.pointEnd hN₃ P = D₁.pointEnd hN₁ P + D₂.pointEnd hN₂ P
  rw [IsogenyEndDatum.pointEnd_apply_eq_sub D₃ hN₃, IsogenyEndDatum.pointEnd_apply_eq_sub D₁ hN₁,
    IsogenyEndDatum.pointEnd_apply_eq_sub D₂ hN₂, hD₃ P, hD₃ 0,
    pointEquivPlace_symm_placeOfPoint, pointEquivPlace_symm_placeOfPoint]
  abel

end S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_pointEnd_eq_add
end P2MW
export P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_pointEnd_eq_add (solution)
