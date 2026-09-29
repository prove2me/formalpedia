-- Prove2me | solution 1 for WeierstrassCurve.Affine.pointMapOfPushforward_surjective_of_separableAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/71ba8eb8-0aa8-5814-88d4-db8213cae087

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_pointMapOfPushforward_surjective_of_separableAlong
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C"
p2m_attr_erase "simp" "ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_pointMapOfPushforward_surjective_of_separableAlong.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_pointMapOfPushforward_surjective_of_separableAlong.WeierstrassCurve.Affine AlgebraicCurve"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map mk IsIntegral"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "map FunctionField Point pointMapOfPushforward GenusOnePlaceGate deg_eq_one pointClass AbelTheorem genusOnePic0Equiv genusOnePic0Equiv_symm_apply"
namespace CharFreePMOP
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

universe u

variable {F : Type u} [Field F] [DecidableEq F]
variable {V W : Affine F}
variable [GenusOnePlaceGate V] [AbelTheorem V] [GenusOnePlaceGate W] [AbelTheorem W]
variable (ι : V.FunctionField →ₐ[F] W.FunctionField) (hι : ι.toRingHom.IsIntegral)

theorem inertiaDegAlong_eq_one' (w : AlgebraicCurve.Place F W.FunctionField) :
    w.inertiaDegAlong ι hι = 1 := by
  have h := AlgebraicCurve.Place.deg_restrictAlong_mul_inertiaDegAlong ι hι w
  rw [deg_eq_one (W := V) (w.restrictAlong ι hι), deg_eq_one (W := W) w, one_mul] at h
  exact h

theorem pushforwardAlong_single_eq' (w : AlgebraicCurve.Place F W.FunctionField) (n : ℤ) :
    Divisor.pushforwardAlong ι hι (Finsupp.single w n)
      = Finsupp.single (w.restrictAlong ι hι) n := by
  rw [Divisor.pushforwardAlong_single, inertiaDegAlong_eq_one' ι hι w, Nat.cast_one, mul_one]

variable (hfin : FiniteAlong F ι) (hN : NormFormulaAlong F ι hfin)

theorem pointMapOfPushforward_apply' (P : W.Point) :
    pointMapOfPushforward ι hι hfin hN P
      = genusOnePic0Equiv V (Pic0.pushforwardAlongHom ι hι hfin hN (pointClass P)) := by
  rw [← genusOnePic0Equiv_symm_apply]
  rfl

end WeierstrassCurve.Affine.CharFreePMOP

end

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_pointMapOfPushforward_surjective_of_separableAlong.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_pointMapOfPushforward_surjective_of_separableAlong.WeierstrassCurve.Affine AlgebraicCurve P2MW.S_WeierstrassCurve_Affine_pointMapOfPushforward_surjective_of_separableAlong.WeierstrassCurve.Affine.CharFreePMOP"

universe u

theorem solution
    {F : Type u} [Field F] [DecidableEq F]
    (E E' : WeierstrassCurve.Affine F) [GenusOnePlaceGate E] [AbelTheorem E]
    [GenusOnePlaceGate E'] [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[F] E.FunctionField) (hι : ι.toRingHom.IsIntegral)
    (hfin : FiniteAlong F ι) (hsep : SeparableAlong F ι) (hN : NormFormulaAlong F ι hfin) :
    Function.Surjective (pointMapOfPushforward ι hι hfin hN) := by
  classical

  choose s hs using AlgebraicCurve.Place.restrictAlong_surjective ι hι hfin hsep

  have hpush : Function.Surjective (Pic0.pushforwardAlongHom ι hι hfin hN) := by
    intro c'
    obtain ⟨D', rfl⟩ := Pic0.mk_surjective c'
    let D : Divisor F E.FunctionField := Finsupp.mapDomain s (D' : Divisor F E'.FunctionField)
    have hD : Divisor.pushforwardAlong ι hι D = (D' : Divisor F E'.FunctionField) := by
      show Divisor.pushforwardAlong ι hι (Finsupp.mapDomain s (D' : Divisor F E'.FunctionField)) = _
      rw [Finsupp.mapDomain, map_finsuppSum]
      conv_rhs => rw [← Finsupp.sum_single (D' : Divisor F E'.FunctionField)]
      refine Finsupp.sum_congr (fun v _ => ?_)
      have hsv : (s v).restrictAlong ι hι = v := hs v
      rw [pushforwardAlong_single_eq' ι hι (s v), hsv]
    have hD0 : D ∈ Divisor.degZero (K := F) (F := E.FunctionField) := by
      rw [Divisor.mem_degZero, ← Divisor.degree_pushforwardAlong ι hι D, hD]
      exact Divisor.mem_degZero.mp D'.2
    refine ⟨Pic0.mk ⟨D, hD0⟩, ?_⟩
    rw [Pic0.pushforwardAlongHom_mk]
    congr 1
    exact Subtype.ext (by rw [Pic0.coe_pushforwardAlongDegZero]; exact hD)

  intro Q
  obtain ⟨c, hc⟩ := hpush ((genusOnePic0Equiv E').symm Q)
  refine ⟨genusOnePic0Equiv E c, ?_⟩
  rw [pointMapOfPushforward_apply', ← genusOnePic0Equiv_symm_apply, AddEquiv.symm_apply_apply, hc,
    AddEquiv.apply_symm_apply]

end S_WeierstrassCurve_Affine_pointMapOfPushforward_surjective_of_separableAlong
end P2MW
export P2MW.S_WeierstrassCurve_Affine_pointMapOfPushforward_surjective_of_separableAlong (solution)
