-- Prove2me | solution 1 for WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/4f9294dd-b7f9-5556-ad59-3851a2ac7a1b

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Theorems.Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_forall_pointEnd_eq_zsmul_of_transcendental_j
import Theorems.Thm_WeierstrassCurve_zmultiples_eq_of_veluQuotient_j_eq_of_forall_isogenyEndDatum_exists_int
import Theorems.Thm_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem
import Theorems.Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField
import Theorems.Thm_HahnSeries_isAlgClosed_rat
import Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain
import Theorems.Thm_AlgebraicCurve_normFormulaAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_zmultiples_eq_of_veluQuotient_j_eq_of_transcendental
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one"
p2m_attr_erase "simp" "compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty"

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

noncomputable section

namespace Ws13B

theorem charZero_hahn : CharZero (HahnSeries ℚ (AlgebraicClosure ℚ)) :=
  (RingHom.charZero_iff (HahnSeries.C (R := AlgebraicClosure ℚ) (Γ := ℚ)).injective).mp inferInstance

theorem normFormulaAlong_of_elliptic {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {V W : Affine F} [V.IsElliptic] [W.IsElliptic] (ι : V.FunctionField →ₐ[F] W.FunctionField)
    (hfin : FiniteAlong F ι) : NormFormulaAlong F ι hfin := by
  haveI : HasPrincipalDivisors F W.FunctionField := hasPrincipalDivisors_functionField W
  haveI : CharZero V.FunctionField :=
    charZero_of_injective_algebraMap (algebraMap F V.FunctionField).injective
  have hsep : SeparableAlong F ι := by
    letI := algebraAlong ι
    haveI := isScalarTower_along ι
    haveI : Module.Finite V.FunctionField W.FunctionField := hfin
    show Algebra.IsSeparable V.FunctionField W.FunctionField
    infer_instance
  exact AlgebraicCurve.normFormulaAlong ι hfin hsep

end Ws13B

end

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve in
theorem solution
    [DecidableEq (HahnSeries ℚ (AlgebraicClosure ℚ))]
    (W : WeierstrassCurve (HahnSeries ℚ (AlgebraicClosure ℚ))) [W.IsElliptic]
    (ht : Transcendental ℚ W.j) (n : ℕ) (Q Q' : W.toAffine.Point)
    (hQ : addOrderOf Q = 2 * n + 1) (hQ' : addOrderOf Q' = 2 * n + 1)
    (hΔ : (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0)
    (hΔ' : (W.veluQuotient (W.oddOrderSummingSet Q' n)).Δ ≠ 0)
    (hj : haveI : (W.veluQuotient (W.oddOrderSummingSet Q n)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
      haveI : (W.veluQuotient (W.oddOrderSummingSet Q' n)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ'⟩
      (W.veluQuotient (W.oddOrderSummingSet Q n)).j = (W.veluQuotient (W.oddOrderSummingSet Q' n)).j) :
    AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q' := by
  haveI : CharZero (HahnSeries ℚ (AlgebraicClosure ℚ)) := Ws13B.charZero_hahn
  haveI : IsAlgClosed (HahnSeries ℚ (AlgebraicClosure ℚ)) := HahnSeries.isAlgClosed_rat
  haveI : IsDedekindDomain W.toAffine.CoordinateRing := CoordinateRing.isDedekindDomain W
  haveI : HasPrincipalDivisors (HahnSeries ℚ (AlgebraicClosure ℚ)) W.toAffine.FunctionField :=
    hasPrincipalDivisors_functionField W.toAffine
  obtain ⟨g, hc, ha⟩ := exists_genusOnePlaceGate_isCentred_and_abelTheorem (W := W.toAffine)
  letI : GenusOnePlaceGate W.toAffine := g
  haveI : GenusOnePlaceGate.IsCentred W.toAffine := hc
  haveI : AbelTheorem W.toAffine := ha
  have hNs : ∀ D : IsogenyEndDatum W.toAffine,
      NormFormulaAlong (HahnSeries ℚ (AlgebraicClosure ℚ)) D.ι D.hfin :=
    fun D => Ws13B.normFormulaAlong_of_elliptic D.ι D.hfin

  have ht' : @Transcendental ℚ (HahnSeries ℚ (AlgebraicClosure ℚ)) _ _ DivisionRing.toRatAlgebra W.j := by
    convert ht using 2 <;> first | rfl | exact Subsingleton.elim _ _
  exact zmultiples_eq_of_veluQuotient_j_eq_of_forall_isogenyEndDatum_exists_int W hNs
    (fun D => IsogenyEndDatum.exists_forall_pointEnd_eq_zsmul_of_transcendental_j W hNs ht' D)
    n Q Q' hQ hQ' hΔ hΔ' hj

end S_WeierstrassCurve_zmultiples_eq_of_veluQuotient_j_eq_of_transcendental
end P2MW
export P2MW.S_WeierstrassCurve_zmultiples_eq_of_veluQuotient_j_eq_of_transcendental (solution)
