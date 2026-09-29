-- Prove2me | solution 1 for WeierstrassCurve.Affine.IsogenyHomDatum.exists_algEquiv_of_ker_le_of_finrankAlong_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/6d84ee07-d041-5b85-95ed-4028d51fe073

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Theorems.Thm_WeierstrassCurve_Affine_IsogenyHomDatum_exists_pointHom_comp_eq_of_ker_le_of_separableAlong
import Theorems.Thm_WeierstrassCurve_Affine_IsogenyHomDatum_pointHom_apply_eq_pointEquivPlace_sub
import Theorems.Thm_AlgebraicCurve_finrankAlong_comp
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_restrictAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_IsogenyHomDatum_exists_algEquiv_of_ker_le_of_finrankAlong_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul"
p2m_attr_erase "simp" "ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

p2m_open "WeierstrassCurve WeierstrassCurve.Affine~pointHom AlgebraicCurve"

universe u

namespace S13Iso

variable {K A B : Type*} [Field K] [Field A] [Field B] [Algebra K A] [Algebra K B]

theorem restrictAlong_congr {φ₁ φ₂ : A →ₐ[K] B} (h : φ₁ = φ₂)
    (h₁ : φ₁.toRingHom.IsIntegral) (h₂ : φ₂.toRingHom.IsIntegral) (w : Place K B) :
    w.restrictAlong φ₁ h₁ = w.restrictAlong φ₂ h₂ := by subst h; rfl

end S13Iso

open S13Iso in
theorem solution
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F]
    {V₀ V₁ V₂ : WeierstrassCurve.Affine F} [V₀.IsElliptic] [GenusOnePlaceGate V₀] [AbelTheorem V₀]
    [V₁.IsElliptic] [GenusOnePlaceGate V₁] [AbelTheorem V₁] [V₂.IsElliptic] [GenusOnePlaceGate V₂] [AbelTheorem V₂]
    [GenusOnePlaceGate.IsCentred V₀]
    (φ : IsogenyHomDatum V₀ V₁) (hsepφ : SeparableAlong F φ.ι) (hNφ : NormFormulaAlong F φ.ι φ.hfin)
    (hφ0 : (placeOfPoint (0 : V₀.Point)).restrictAlong φ.ι φ.hι = placeOfPoint (0 : V₁.Point))
    (ψ : IsogenyHomDatum V₀ V₂) (hsepψ : SeparableAlong F ψ.ι) (hNψ : NormFormulaAlong F ψ.ι ψ.hfin)
    (hψ0 : (placeOfPoint (0 : V₀.Point)).restrictAlong ψ.ι ψ.hι = placeOfPoint (0 : V₂.Point))
    (hker : ∀ P : V₀.Point, φ.pointHom hNφ P = 0 → ψ.pointHom hNψ P = 0)
    (hdeg : finrankAlong F φ.ι = finrankAlong F ψ.ι) :
    ∃ (e : V₂.FunctionField ≃ₐ[F] V₁.FunctionField) (he : e.toAlgHom.toRingHom.IsIntegral)
      (g : V₁.Point →+ V₂.Point),
      φ.ι.comp e.toAlgHom = ψ.ι ∧
      (∀ P : V₀.Point, g (φ.pointHom hNφ P) = ψ.pointHom hNψ P) ∧
      ∀ P₁ : V₁.Point, (placeOfPoint P₁).restrictAlong e.toAlgHom he = placeOfPoint (g P₁) := by
  obtain ⟨χ, hsepχ, hNχ, hcomp, hpt⟩ :=
    IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_separableAlong φ hsepφ hNφ ψ hsepψ hNψ hker

  have hmul : finrankAlong F ψ.ι = finrankAlong F χ.ι * finrankAlong F φ.ι := by
    rw [← hcomp]; exact AlgebraicCurve.finrankAlong_comp χ.ι φ.ι
  have hψpos : 0 < finrankAlong F ψ.ι := by
    letI := algebraAlong ψ.ι
    haveI : Module.Finite V₂.FunctionField V₀.FunctionField := ψ.hfin
    exact Module.finrank_pos
  have hχ1 : finrankAlong F χ.ι = 1 := by
    rw [hdeg] at hmul
    exact Nat.eq_of_mul_eq_mul_right hψpos (hmul.symm.trans (one_mul _).symm)

  have hsurj : Function.Surjective χ.ι := by
    letI := algebraAlong χ.ι
    haveI : Module.Finite V₂.FunctionField V₁.FunctionField := χ.hfin
    have h1 : Module.finrank V₂.FunctionField V₁.FunctionField = 1 := hχ1
    intro y
    have hy : y ∈ (⊥ : Subalgebra V₂.FunctionField V₁.FunctionField) := by
      rw [Subalgebra.bot_eq_top_of_finrank_eq_one h1]; exact Algebra.mem_top
    obtain ⟨x, hx⟩ := Algebra.mem_bot.mp hy
    exact ⟨x, hx⟩
  let e : V₂.FunctionField ≃ₐ[F] V₁.FunctionField :=
    AlgEquiv.ofBijective χ.ι ⟨RingHom.injective χ.ι.toRingHom, hsurj⟩
  have he_coe : e.toAlgHom = χ.ι := rfl

  have hint : (φ.ι.comp χ.ι).toRingHom.IsIntegral := RingHom.IsIntegral.trans _ _ χ.hι φ.hι
  have hχ0 : (placeOfPoint (0 : V₁.Point)).restrictAlong χ.ι χ.hι = placeOfPoint (0 : V₂.Point) := by
    rw [← hφ0, Place.restrictAlong_restrictAlong χ.ι φ.ι χ.hι φ.hι hint,
      restrictAlong_congr hcomp hint ψ.hι, hψ0]
  refine ⟨e, χ.hι, χ.pointHom hNχ, hcomp, hpt, fun P₁ => ?_⟩
  have hrig := IsogenyHomDatum.pointHom_apply_eq_pointEquivPlace_sub χ hNχ P₁
  rw [hχ0, show (pointEquivPlace (W := V₂)).symm (placeOfPoint (0 : V₂.Point)) = 0 from
    (pointEquivPlace (W := V₂)).symm_apply_apply 0, sub_zero] at hrig
  show (placeOfPoint P₁).restrictAlong χ.ι χ.hι = placeOfPoint (χ.pointHom hNχ P₁)
  rw [hrig]
  exact ((pointEquivPlace (W := V₂)).apply_symm_apply _).symm

end
end S_WeierstrassCurve_Affine_IsogenyHomDatum_exists_algEquiv_of_ker_le_of_finrankAlong_eq
end P2MW
export P2MW.S_WeierstrassCurve_Affine_IsogenyHomDatum_exists_algEquiv_of_ker_le_of_finrankAlong_eq (solution)
