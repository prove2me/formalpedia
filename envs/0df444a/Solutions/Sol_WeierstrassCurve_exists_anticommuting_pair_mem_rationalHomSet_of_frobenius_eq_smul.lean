-- Prove2me | solution 1 for WeierstrassCurve.exists_anticommuting_pair_mem_rationalHomSet_of_frobenius_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/ef316738-5a11-5d42-8711-2cf9c2a133f3

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_DualIsogenyAPI
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_dualIsogenyExistence_rationalEndSubring
import Theorems.Thm_WeierstrassCurve_exists_comp_ne_comp_of_frobenius_eq_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_anticommuting_pair_mem_rationalHomSet_of_frobenius_eq_smul
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY a₃ a₁ map toAffine Affine.Point Affine.nonsingular_neg Affine.Point.map baseChange j evalEvalBC rationalHomSet rationalEndSubring zero_mem_rationalHomSet id_mem_rationalHomSet add_mem_rationalHomSet comp_mem_rationalHomSet surjective_of_mem_rationalHomSet card_torsion_of_isAlgClosed dualIsogenyExistence_rationalEndSubring exists_comp_ne_comp_of_frobenius_eq_smul"
namespace DeuringQuaternion
p2m_open "WeierstrassCurve"

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k]

noncomputable def bc (x y : k) : F[X][Y] →+* k :=
  (evalEvalRingHom x y).comp (mapRingHom (mapRingHom (algebraMap F k)))

theorem evalEvalBC_eq (p : F[X][Y]) (x y : k) : WeierstrassCurve.evalEvalBC k p x y = bc x y p := rfl

@[scoped simp] theorem bc_CC (x y : k) (a : F) : bc x y (C (C a)) = algebraMap F k a := by
  simp [bc]

variable [DecidableEq k]

abbrev Pt (k : Type*) [Field k] [Algebra F k] (W : WeierstrassCurve F) :=
  (W.baseChange k).toAffine.Point

omit [DecidableEq k] in
theorem exists_some_of_eq (W : WeierstrassCurve F) {Q : Pt k W} {x₁ y₁ : k}
    {h₁ : (W.baseChange k).toAffine.Nonsingular x₁ y₁}
    (hQ : Q = .some x₁ y₁ h₁) {x₂ y₂ : k} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    ∃ h₂, Q = .some x₂ y₂ h₂ := by
  subst hx hy; exact ⟨h₁, hQ⟩

variable {W : WeierstrassCurve F}

theorem neg_mem {α : Pt k W →+ Pt k W} (hα : α ∈ rationalHomSet k W W) :
    -α ∈ rationalHomSet k W W := by
  rcases hα with rfl | ⟨nX, dX, nY, dY, B, hB, hrep⟩
  · rw [neg_zero]; exact zero_mem_rationalHomSet k W W
  refine Or.inr ⟨nX, dX, -(nY * dX) - C (C W.a₁) * nX * dY - C (C W.a₃) * dX * dY, dY * dX,
    B, hB, ?_⟩
  intro x y h hx
  obtain ⟨hdX, hdY, h', hP⟩ := hrep x y h hx
  simp only [evalEvalBC_eq] at hdX hdY hP ⊢
  refine ⟨hdX, by rw [map_mul]; exact mul_ne_zero hdY hdX, ?_⟩
  have hneg : (-α) (.some x y h) =
      .some (bc x y nX / bc x y dX)
        ((W.baseChange k).toAffine.negY (bc x y nX / bc x y dX) (bc x y nY / bc x y dY))
        ((Affine.nonsingular_neg ..).mpr h') := by
    rw [AddMonoidHom.neg_apply, hP]; rfl
  refine exists_some_of_eq W hneg rfl ?_
  simp only [Affine.negY, map_sub, map_neg, map_mul, bc_CC]
  change -(bc x y nY / bc x y dY) - algebraMap F k W.a₁ * (bc x y nX / bc x y dX)
      - algebraMap F k W.a₃ = _
  field_simp

variable [IsAlgClosed k] [W.IsElliptic]

theorem add_mem {α β : Pt k W →+ Pt k W} (hα : α ∈ rationalHomSet k W W)
    (hβ : β ∈ rationalHomSet k W W) : α + β ∈ rationalHomSet k W W :=
  WeierstrassCurve.add_mem_rationalHomSet k W W hα hβ

theorem sub_mem {α β : Pt k W →+ Pt k W} (hα : α ∈ rationalHomSet k W W)
    (hβ : β ∈ rationalHomSet k W W) : α - β ∈ rationalHomSet k W W := by
  rw [sub_eq_add_neg]; exact add_mem hα (neg_mem hβ)

theorem zsmul_mem {α : Pt k W →+ Pt k W} (hα : α ∈ rationalHomSet k W W) (c : ℤ) :
    c • α ∈ rationalHomSet k W W := by
  induction c using Int.induction_on with
  | zero => rw [zero_zsmul]; exact zero_mem_rationalHomSet k W W
  | succ n ih => rw [add_zsmul, one_zsmul]; exact add_mem ih hα
  | pred n ih => rw [sub_zsmul, one_zsmul]; exact sub_mem ih hα

omit [IsAlgClosed k] [W.IsElliptic] in
theorem comp_mem {α β : Pt k W →+ Pt k W} (hα : α ∈ rationalHomSet k W W)
    (hβ : β ∈ rationalHomSet k W W) : α.comp β ∈ rationalHomSet k W W :=
  WeierstrassCurve.comp_mem_rationalHomSet k W W W hβ hα

omit [DecidableEq k] [IsAlgClosed k] [W.IsElliptic] in

theorem exists_prime_not_dvd (m : ℤ) (hm : m ≠ 0) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ¬ ((ℓ : ℤ) ∣ m) ∧ (ℓ : k) ≠ 0 := by
  obtain ⟨ℓ, hℓge, hℓp⟩ := Nat.exists_infinite_primes (m.natAbs + ringChar k + 1)
  refine ⟨ℓ, hℓp, fun hdvd => ?_, fun h0 => ?_⟩
  · have h1 : ℓ ∣ m.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr hdvd
      simpa using this
    have h2 : ℓ ≤ m.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hm) h1
    omega
  · have := CharP.ringChar_of_prime_eq_zero hℓp h0
    omega

theorem exists_zsmul_ne_zero (m : ℤ) (hm : m ≠ 0) : ∃ Q : Pt k W, m • Q ≠ 0 := by
  obtain ⟨ℓ, hℓp, hℓm, hℓk⟩ := exists_prime_not_dvd (k := k) m hm
  have hcard : Nat.card (Submodule.torsionBy ℤ (Pt k W) (ℓ : ℤ)) = ℓ ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (K := k) W (n := ℓ) hℓk
  haveI : Finite (Submodule.torsionBy ℤ (Pt k W) (ℓ : ℤ)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hℓp.ne_zero)
  have h1 : 1 < Nat.card (Submodule.torsionBy ℤ (Pt k W) (ℓ : ℤ)) := by
    rw [hcard]
    have := hℓp.one_lt
    nlinarith
  haveI : Nontrivial (Submodule.torsionBy ℤ (Pt k W) (ℓ : ℤ)) :=
    Finite.one_lt_card_iff_nontrivial.mp h1
  obtain ⟨⟨T, hT⟩, hT0⟩ := exists_ne (0 : Submodule.torsionBy ℤ (Pt k W) (ℓ : ℤ))
  have hTℓ : (ℓ : ℤ) • T = 0 := (Submodule.mem_torsionBy_iff _ _).mp hT
  have hTne : T ≠ 0 := fun h => hT0 (Subtype.ext h)
  refine ⟨T, fun hmT => hTne ?_⟩
  have hcop : IsCoprime (ℓ : ℤ) m := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h1 : ¬ ℓ ∣ m.natAbs := fun h => hℓm (Int.natAbs_dvd_natAbs.mp (by simpa using h))
    have h2 : Nat.Coprime ℓ m.natAbs := (Nat.Prime.coprime_iff_not_dvd hℓp).mpr h1
    simpa [Int.gcd] using h2
  obtain ⟨c, d, hcd⟩ := hcop
  calc T = (1 : ℤ) • T := (one_zsmul T).symm
    _ = (c * ℓ + d * m) • T := by rw [hcd]
    _ = 0 := by rw [add_zsmul, mul_smul, mul_smul, hTℓ, hmT, smul_zero, smul_zero, add_zero]

theorem eq_zero_of_zsmul_eq_zero {δ : Pt k W →+ Pt k W} (hδ : δ ∈ rationalHomSet k W W)
    {m : ℤ} (hm : m ≠ 0) (h : ∀ P, m • δ P = 0) : δ = 0 := by
  by_contra hne
  have hs := WeierstrassCurve.surjective_of_mem_rationalHomSet k hδ hne
  obtain ⟨Q, hQ⟩ := exists_zsmul_ne_zero (k := k) (W := W) m hm
  obtain ⟨P, rfl⟩ := hs Q
  exact hQ (h P)

omit [DecidableEq k] [IsAlgClosed k] [W.IsElliptic] in

theorem eq_zero_of_comp_eq_zero [DecidableEq k] [IsAlgClosed k] [W.IsElliptic]
    {γ δ : Pt k W →+ Pt k W} (hδ : δ ∈ rationalHomSet k W W)
    (hδ0 : δ ≠ 0) (h : ∀ P, γ (δ P) = 0) : γ = 0 := by
  have hs := WeierstrassCurve.surjective_of_mem_rationalHomSet k hδ hδ0
  ext Q
  obtain ⟨P, rfl⟩ := hs Q
  exact h P

theorem eq_zero_of_comp_self {δ : Pt k W →+ Pt k W} (hδ : δ ∈ rationalHomSet k W W)
    (h : ∀ P, δ (δ P) = 0) : δ = 0 := by
  by_contra hne
  exact hne (eq_zero_of_comp_eq_zero hδ hne h)

theorem exists_quadratic {α : Pt k W →+ Pt k W} (hα : α ∈ rationalHomSet k W W) :
    ∃ t n : ℤ, ∀ P, α (α P) = t • α P - n • P := by
  have hmem : (α : AddMonoid.End (Pt k W)) ∈ rationalEndSubring k W :=
    Subring.subset_closure hα
  have hq := WeierstrassCurve.dualIsogenyExistence_rationalEndSubring k W
  obtain ⟨D, -, -⟩ := hq α hmem
  refine ⟨D.trace, D.norm, fun P => ?_⟩
  have h : α (α P) - D.trace • α P + D.norm • P = 0 := D.charPoly_apply P
  calc α (α P) = (α (α P) - D.trace • α P + D.norm • P) + (D.trace • α P - D.norm • P) := by
        abel
    _ = D.trace • α P - D.norm • P := by rw [h, zero_add]

theorem main (hnc : ∃ α ∈ rationalHomSet k W W, ∃ β ∈ rationalHomSet k W W,
      α.comp β ≠ β.comp α) :
    ∃ i ∈ rationalHomSet k W W, ∃ j ∈ rationalHomSet k W W, ∃ u v : ℤ,
      u ≠ 0 ∧ v ≠ 0 ∧ (∀ P, i (i P) = u • P) ∧ (∀ P, j (j P) = v • P) ∧
        (∀ P, i (j P) = -(j (i P))) := by
  obtain ⟨α, hα, β, hβ, hne⟩ := hnc
  obtain ⟨t, n, hq⟩ := exists_quadratic hα

  set i : Pt k W →+ Pt k W := (2 : ℤ) • α - t • AddMonoidHom.id (Pt k W) with hi_def
  have hi : i ∈ rationalHomSet k W W :=
    sub_mem (zsmul_mem hα 2) (zsmul_mem (id_mem_rationalHomSet k W) t)
  have hi_apply : ∀ P, i P = (2 : ℤ) • α P - t • P := fun P => rfl
  have hii : ∀ P, i (i P) = (t * t - 4 * n) • P := by
    intro P
    rw [hi_apply, hi_apply, map_sub, map_zsmul, map_zsmul, hq P]
    module

  set j : Pt k W →+ Pt k W := i.comp β - β.comp i with hj_def
  have hj : j ∈ rationalHomSet k W W := sub_mem (comp_mem hi hβ) (comp_mem hβ hi)
  have hj_apply : ∀ P, j P = i (β P) - β (i P) := fun P => rfl

  have hj0 : j ≠ 0 := by
    intro hj0
    apply hne
    have hδ : α.comp β - β.comp α ∈ rationalHomSet k W W :=
      sub_mem (comp_mem hα hβ) (comp_mem hβ hα)
    have h2 : ∀ P, (2 : ℤ) • (α.comp β - β.comp α) P = 0 := by
      intro P
      have hP : j P = 0 := by rw [hj0]; rfl
      rw [hj_apply, hi_apply, hi_apply, map_sub, map_zsmul, map_zsmul] at hP
      rw [AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← hP]
      module
    exact sub_eq_zero.mp (eq_zero_of_zsmul_eq_zero hδ two_ne_zero h2)

  have hi0 : i ≠ 0 := by
    intro hi0
    apply hj0
    ext P
    rw [hj_apply, hi0]
    simp
  have hu : t * t - 4 * n ≠ 0 := by
    intro hu
    exact hi0 (eq_zero_of_comp_self hi fun P => by rw [hii, hu, zero_zsmul])

  have hanti : ∀ P, i (j P) = -(j (i P)) := by
    intro P
    rw [hj_apply, hj_apply, map_sub, hii, hii, map_zsmul]
    abel

  obtain ⟨t', n', hq'⟩ := exists_quadratic hj
  have hij0 : i.comp j ≠ 0 := fun h0 =>
    hi0 (eq_zero_of_comp_eq_zero hj hj0 fun P => DFunLike.congr_fun h0 P)
  have ht' : t' = 0 := by
    have h2 : ∀ Q, ((2 : ℤ) * t') • (i.comp j) Q = 0 := by
      intro Q

      have e : i (j (j Q)) = j (j (i Q)) := by
        rw [hanti (j Q), hanti Q, map_neg, neg_neg]
      rw [hq' Q, hq' (i Q), map_sub, map_zsmul, map_zsmul, hanti Q, smul_neg, sub_left_inj,
        neg_eq_iff_add_eq_zero] at e
      show ((2 : ℤ) * t') • i (j Q) = 0
      rw [hanti Q, smul_neg, neg_eq_zero, mul_smul, two_zsmul]
      exact e
    by_contra ht
    exact hij0 (eq_zero_of_zsmul_eq_zero (comp_mem hi hj) (mul_ne_zero two_ne_zero ht) h2)
  have hjj : ∀ P, j (j P) = (-n') • P := by
    intro P
    rw [hq' P, ht', zero_zsmul, zero_sub, neg_smul]
  have hv : -n' ≠ 0 := by
    intro hv
    exact hj0 (eq_zero_of_comp_self hj fun P => by rw [hjj, hv, zero_zsmul])
  exact ⟨i, hi, j, hj, t * t - 4 * n, -n', hu, hv, hii, hjj, hanti⟩

end WeierstrassCurve.DeuringQuaternion
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_anticommuting_pair_mem_rationalHomSet_of_frobenius_eq_smul.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_anticommuting_pair_mem_rationalHomSet_of_frobenius_eq_smul.WeierstrassCurve.DeuringQuaternion"
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_anticommuting_pair_mem_rationalHomSet_of_frobenius_eq_smul.WeierstrassCurve"

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_anticommuting_pair_mem_rationalHomSet_of_frobenius_eq_smul.WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point"

theorem solution {F : Type*} [Field F] [Fintype F] (k : Type*) [Field k] [DecidableEq k] [Algebra F k] [IsAlgClosed k] [Algebra.IsAlgebraic F k] (W : WeierstrassCurve F) [W.IsElliptic] (σ : k →ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) (a : ℤ) (ha : ∀ P : (W⁄k).Point, WeierstrassCurve.Affine.Point.map (W' := W) σ P = a • P) : ∃ i ∈ WeierstrassCurve.rationalHomSet k W W, ∃ j ∈ WeierstrassCurve.rationalHomSet k W W, ∃ u v : ℤ, u ≠ 0 ∧ v ≠ 0 ∧ (∀ P, i (i P) = u • P) ∧ (∀ P, j (j P) = v • P) ∧ (∀ P, i (j P) = -(j (i P))) :=
  WeierstrassCurve.DeuringQuaternion.main
    (WeierstrassCurve.exists_comp_ne_comp_of_frobenius_eq_smul k W σ hσ a ha)

end S_WeierstrassCurve_exists_anticommuting_pair_mem_rationalHomSet_of_frobenius_eq_smul
end P2MW
export P2MW.S_WeierstrassCurve_exists_anticommuting_pair_mem_rationalHomSet_of_frobenius_eq_smul (solution)
