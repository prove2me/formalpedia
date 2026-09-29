-- Prove2me | solution 1 for WeierstrassCurve.residue_cyclicQuotientJ_eq_cyclicQuotientJ_map_reduceHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/310e0bff-6573-5fca-bba5-07fb4cd68089

import Mathlib
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Theorems.Thm_WeierstrassCurve_stepCurve_stepSubgroup_eq_of_prime_ne_two
import Theorems.Thm_WeierstrassCurve_stepCurve_stepSubgroup_two_eq
import Theorems.Thm_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2
import Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow
import Theorems.Thm_WeierstrassCurve_veluQuotient2_Delta_ne_zero
import Theorems.Thm_WeierstrassCurve_exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom
import Theorems.Thm_WeierstrassCurve_veluX_mem_and_residue_veluX_eq_of_forall_fst_ne_residue
import Theorems.Thm_WeierstrassCurve_addOrderOf_reduceHom_of_natCast_ne_zero
import Theorems.Thm_WeierstrassCurve_eq_of_reduceHom_eq_of_nsmul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_residue_cyclicQuotientJ_eq_cyclicQuotientJ_map_reduceHom
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000

p2m_open "WeierstrassCurve~map_veluGy~map_veluGx P2MW.S_WeierstrassCurve_residue_cyclicQuotientJ_eq_cyclicQuotientJ_map_reduceHom.WeierstrassCurve IsLocalRing"

universe u

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map_c₄ Affine.negY Affine.Y_eq_of_Y_ne map map_b₂ coe_Δ' Affine.Point.some Affine.Point.some.inj reduction toAffine Affine.Point map_Δ Affine.Point.some_ne_zero Δ c₄ Affine.Y_eq_of_X_eq Affine.Point.neg_some j Δ' stepCurve stepSubgroup cyclicQuotientJ cyclicQuotientJ_one cyclicQuotientJ_eq_of_two_le veluGx veluGy veluGy_eq_zero_of_negY_eq veluQuotient veluQuotient2 velu2X velu2Y velu2_map_nonsingular veluPointMap2 veluPointMap2_some_of_eq veluPointMap2_some_of_ne Affine.Point.coordsOrZero_some oddOrderSummingSet mem_oddOrderSummingSet reduceHom X_mem_of_nsmul_eq_zero' Affine.Y_mem_of_X_mem Affine.nonsingular_residue reducePoint_some_of_mem veluX veluY stepCurve_stepSubgroup_eq_of_prime_ne_two stepCurve_stepSubgroup_two_eq exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed exists_addMonoidHom_coe_eq_veluPointMap2 veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow veluQuotient2_Delta_ne_zero exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom veluX_mem_and_residue_veluX_eq_of_forall_fst_ne_residue addOrderOf_reduceHom_of_natCast_ne_zero eq_of_reduceHom_eq_of_nsmul_eq_zero"
p2m_open "WeierstrassCurve~map_veluGy~map_veluGx"
namespace CQJReduce

section Cast

variable {F : Type*} [Field F] [DecidableEq F]

def castHom {V₁ V₂ : WeierstrassCurve F} (h : V₁ = V₂) :
    V₁.toAffine.Point ≃+ V₂.toAffine.Point := by subst h; exact AddEquiv.refl _

theorem castHom_some {V₁ V₂ : WeierstrassCurve F} (h : V₁ = V₂)
    (x y : F) (h₁ : V₁.toAffine.Nonsingular x y) :
    castHom h (Affine.Point.some x y h₁) = Affine.Point.some x y (h ▸ h₁) := by subst h; rfl

theorem sigma_castHom {V₁ V₂ : WeierstrassCurve F} (h : V₁ = V₂)
    (H : AddSubgroup V₁.toAffine.Point) :
    (⟨V₂, H.map (castHom h).toAddMonoidHom⟩ : Σ V : WeierstrassCurve F, AddSubgroup V.toAffine.Point) =
      ⟨V₁, H⟩ := by
  subst h
  congr 1
  ext P
  constructor
  · rintro ⟨Q, hQ, rfl⟩; exact hQ
  · intro hP; exact ⟨P, hP, rfl⟩

theorem cyclicQuotientJ_congr {V V' : WeierstrassCurve F}
    {H : AddSubgroup V.toAffine.Point} {H' : AddSubgroup V'.toAffine.Point}
    (h : (⟨V, H⟩ : Σ V : WeierstrassCurve F, AddSubgroup V.toAffine.Point) = ⟨V', H'⟩) (n : ℕ) :
    V.cyclicQuotientJ H n = V'.cyclicQuotientJ H' n := by
  cases h; rfl

theorem some_congr {V : WeierstrassCurve F} {x₁ x₂ y₁ y₂ : F}
    (hx : x₁ = x₂) (hy : y₁ = y₂) (h₁ : V.toAffine.Nonsingular x₁ y₁) (h₂ : V.toAffine.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

theorem exists_eq_some_of_ne_zero {V : WeierstrassCurve F} {P : V.toAffine.Point} (hP : P ≠ 0) :
    ∃ x y h, P = Affine.Point.some x y h := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · exact ⟨x, y, h, rfl⟩

theorem eq_or_eq_neg_of_fst_eq {V : WeierstrassCurve F} {x y y' : F} (h : V.toAffine.Nonsingular x y)
    (h' : V.toAffine.Nonsingular x y') :
    Affine.Point.some x y' h' = Affine.Point.some x y h ∨
      Affine.Point.some x y' h' = -Affine.Point.some x y h := by
  by_cases hy : y' = V.toAffine.negY x y
  · right
    rw [Affine.Point.neg_some]
    exact some_congr rfl hy _ _
  · left
    exact some_congr rfl (Affine.Y_eq_of_Y_ne h'.left h.left rfl hy) _ _

end Cast

section Groups

abbrev CycSub (G : Type*) [AddCommGroup G] (n : ℕ) : Set (AddSubgroup G) :=
  {H | IsAddCyclic H ∧ Nat.card H = n}

theorem finite_of_mem_cycSub {G : Type*} [AddCommGroup G] {n : ℕ} (hn : n ≠ 0) {H : AddSubgroup G}
    (hH : H ∈ CycSub G n) : Finite H :=
  Nat.finite_of_card_ne_zero (hH.2.symm ▸ hn)

theorem nsmul_eq_zero_of_mem_cycSub {G : Type*} [AddCommGroup G] {n : ℕ} {H : AddSubgroup G}
    (hH : H ∈ CycSub G n) {P : G} (hP : P ∈ H) : n • P = 0 := by
  have := card_nsmul_eq_zero' (G := H) (x := ⟨P, hP⟩)
  rw [hH.2] at this
  exact congrArg Subtype.val this

theorem map_mem_cycSub {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (φ : G →+ G')
    {ℓ M : ℕ} (hℓ : ℓ ≠ 0) {H : AddSubgroup G} (hH : H ∈ CycSub G (ℓ * M))
    (hker : φ.ker ≤ H) (hkercard : Nat.card φ.ker = ℓ) : H.map φ ∈ CycSub G' M := by
  haveI := hH.1
  set ψ : H →+ H.map φ := φ.addSubgroupMap H
  have hψ : Function.Surjective ψ := φ.addSubgroupMap_surjective H
  refine ⟨isAddCyclic_of_surjective ψ hψ, ?_⟩
  have hkerψ : ψ.ker = φ.ker.addSubgroupOf H := by
    ext ⟨h, hh⟩
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker, Subtype.ext_iff]
    rfl
  have hcardker : Nat.card ψ.ker = ℓ := by
    rw [hkerψ, Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hker).toEquiv, hkercard]
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ψ.ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv, hcardker, hH.2,
    mul_comm] at h1
  exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hℓ) h1).symm

theorem map_equiv_mem_cycSub {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (e : G ≃+ G')
    {n : ℕ} {H : AddSubgroup G} (hH : H ∈ CycSub G n) : H.map e.toAddMonoidHom ∈ CycSub G' n := by
  haveI := hH.1
  refine ⟨?_, ?_⟩
  · exact isAddCyclic_of_surjective (e.toAddMonoidHom.addSubgroupMap H)
      (e.toAddMonoidHom.addSubgroupMap_surjective H)
  · rw [AddSubgroup.card_map_of_injective e.injective, hH.2]

theorem map_mem_cycSub_of_injOn {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (f : G →+ G')
    {n : ℕ} {H : AddSubgroup G} (hH : H ∈ CycSub G n) (hf : Set.InjOn f H) :
    H.map f ∈ CycSub G' n := by
  haveI := hH.1
  refine ⟨isAddCyclic_of_surjective (f.addSubgroupMap H) (f.addSubgroupMap_surjective H), ?_⟩
  rw [← hH.2, ← SetLike.coe_sort_coe (H.map f), AddSubgroup.coe_map, Nat.card_image_of_injOn hf,
    SetLike.coe_sort_coe]

theorem exists_mem_addOrderOf_eq {G : Type*} [AddCommGroup G] {n : ℕ} (hn : n ≠ 0)
    {H : AddSubgroup G} (hH : H ∈ CycSub G n) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓn : ℓ ∣ n) :
    ∃ Q ∈ H, addOrderOf Q = ℓ := by
  haveI : Finite H := finite_of_mem_cycSub hn hH
  haveI : Fintype H := Fintype.ofFinite H
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hdvd : ℓ ∣ Fintype.card H := by rw [Fintype.card_eq_nat_card, hH.2]; exact hℓn
  obtain ⟨⟨q, hqH⟩, hq⟩ := exists_prime_addOrderOf_dvd_card ℓ hdvd
  refine ⟨q, hqH, ?_⟩
  rw [← hq]; exact addOrderOf_injective H.subtype Subtype.coe_injective ⟨q, hqH⟩

end Groups

section Reduction

variable {K : Type u} [Field K] [DecidableEq K] {A : ValuationSubring K}
  [DecidableEq (ResidueField A)]

theorem natCast_ne_zero_of_residue {n : ℕ} (hn : (n : ResidueField A) ≠ 0) : (n : K) ≠ 0 := by
  intro h
  apply hn
  have h1 : ((n : A) : K) = (n : K) := by simp
  have h2 : (n : A) = 0 := Subtype.ext (by rw [h1, h]; rfl)
  rw [← map_natCast (residue A) n, h2, map_zero]

theorem coe_Δ_notMem_nonunits {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0) :
    ((W.Δ : A) : K) ∉ A.nonunits := by
  rw [A.coe_mem_nonunits_iff_residue_eq_zero]
  rwa [map_Δ] at hΔ

theorem Δ_generic_ne_zero {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0) :
    (W.map A.subtype).Δ ≠ 0 := by
  rw [map_Δ]
  exact A.ne_zero_of_notMem_nonunits (coe_Δ_notMem_nonunits hΔ)

theorem isElliptic_generic {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0) :
    (W.map A.subtype).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (Δ_generic_ne_zero hΔ)⟩

theorem isElliptic_special {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0) :
    (W.map (residue A)).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr hΔ⟩

theorem reduceHom_some {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0) {x y : K} (h : (W.map A.subtype).toAffine.Nonsingular x y) (hx : x ∈ A) :
    reduceHom hΔ (.some x y h) =
      .some (residue A ⟨x, hx⟩) (residue A ⟨y, Affine.Y_mem_of_X_mem W h.1 hx⟩)
        (Affine.nonsingular_residue W hΔ h.1) :=
  reducePoint_some_of_mem hΔ h hx

theorem injOn_reduceHom {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0) {N : ℕ} (hN : (N : ResidueField A) ≠ 0)
    {H : AddSubgroup (W.map A.subtype).toAffine.Point} (hH : ∀ P ∈ H, N • P = 0) :
    Set.InjOn (reduceHom hΔ) H := fun _ hP _ hQ h =>
  eq_of_reduceHom_eq_of_nsmul_eq_zero hΔ hN (hH _ hP) (hH _ hQ) h

theorem X_mem {W : WeierstrassCurve A} {N : ℕ} (hN : (N : ResidueField A) ≠ 0)
    {H : AddSubgroup (W.map A.subtype).toAffine.Point} (hH : ∀ P ∈ H, N • P = 0)
    {x y : K} {h : (W.map A.subtype).toAffine.Nonsingular x y} (hP : Affine.Point.some x y h ∈ H) :
    x ∈ A :=
  X_mem_of_nsmul_eq_zero' W hN h (hH _ hP)

theorem eq_or_eq_neg_of_residue_X_eq {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0) {N : ℕ} (hN : (N : ResidueField A) ≠ 0)
    {H : AddSubgroup (W.map A.subtype).toAffine.Point} (hH : ∀ P ∈ H, N • P = 0)
    {x₁ y₁ x₂ y₂ : K} {h₁ : (W.map A.subtype).toAffine.Nonsingular x₁ y₁}
    {h₂ : (W.map A.subtype).toAffine.Nonsingular x₂ y₂}
    (hP₁ : Affine.Point.some x₁ y₁ h₁ ∈ H) (hP₂ : Affine.Point.some x₂ y₂ h₂ ∈ H)
    (hx : residue A ⟨x₁, X_mem hN hH hP₁⟩ = residue A ⟨x₂, X_mem hN hH hP₂⟩) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ ∨
      Affine.Point.some x₁ y₁ h₁ = -Affine.Point.some x₂ y₂ h₂ := by
  have hr₁ := reduceHom_some hΔ h₁ (X_mem hN hH hP₁)
  have hr₂ := reduceHom_some hΔ h₂ (X_mem hN hH hP₂)
  have hinj := injOn_reduceHom hΔ hN hH

  have key : reduceHom hΔ (Affine.Point.some x₁ y₁ h₁) = reduceHom hΔ (Affine.Point.some x₂ y₂ h₂) ∨
      reduceHom hΔ (Affine.Point.some x₁ y₁ h₁) = -reduceHom hΔ (Affine.Point.some x₂ y₂ h₂) := by
    rw [hr₁, hr₂]
    have h₂' : (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x₁, X_mem hN hH hP₁⟩)
        (residue A ⟨y₂, Affine.Y_mem_of_X_mem W h₂.1 (X_mem hN hH hP₂)⟩) := by
      rw [hx]; exact Affine.nonsingular_residue W hΔ h₂.1
    have e2 : Affine.Point.some (residue A ⟨x₂, X_mem hN hH hP₂⟩)
        (residue A ⟨y₂, Affine.Y_mem_of_X_mem W h₂.1 (X_mem hN hH hP₂)⟩)
        (Affine.nonsingular_residue W hΔ h₂.1) = Affine.Point.some _ _ h₂' :=
      some_congr hx.symm rfl _ _
    rw [e2]
    exact eq_or_eq_neg_of_fst_eq h₂' _
  rcases key with h | h
  · exact Or.inl (hinj hP₁ hP₂ h)
  · right
    rw [← map_neg] at h
    exact hinj hP₁ (H.neg_mem hP₂) h

theorem mem_of_reduceHom_mem_map {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0) {N : ℕ} (hN : (N : ResidueField A) ≠ 0)
    {H : AddSubgroup (W.map A.subtype).toAffine.Point} (hH : ∀ P ∈ H, N • P = 0)
    {C : AddSubgroup (W.map A.subtype).toAffine.Point} (hC : C ≤ H)
    {P : (W.map A.subtype).toAffine.Point} (hP : P ∈ H) (hPC : reduceHom hΔ P ∈ C.map (reduceHom hΔ)) :
    P ∈ C := by
  obtain ⟨P', hP', h⟩ := hPC
  have := injOn_reduceHom hΔ hN hH (hC hP') hP h
  rwa [← this]

end Reduction

section Step

variable {K : Type u} [Field K] [DecidableEq K] {A : ValuationSubring K}
  [DecidableEq (ResidueField A)]

def Claim (A : ValuationSubring K) [DecidableEq (ResidueField A)] (n : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve A) (hΔ : (W.map (residue A)).Δ ≠ 0)
    (H : AddSubgroup (W.map A.subtype).toAffine.Point),
    H ∈ CycSub (W.map A.subtype).toAffine.Point n →
      ∃ hmem : (W.map A.subtype).cyclicQuotientJ H n ∈ A,
        residue A ⟨_, hmem⟩ = (W.map (residue A)).cyclicQuotientJ (H.map (reduceHom hΔ)) n

structure StepData (W : WeierstrassCurve A) (hΔ : (W.map (residue A)).Δ ≠ 0)
    (H : AddSubgroup (W.map A.subtype).toAffine.Point) (ℓ M : ℕ) where
  Vq : WeierstrassCurve K
  Hq : AddSubgroup Vq.toAffine.Point
  Vr : WeierstrassCurve (ResidueField A)
  Hr : AddSubgroup Vr.toAffine.Point
  W' : WeierstrassCurve A
  eK : W'.map A.subtype = Vq
  ek : W'.map (residue A) = Vr
  σK : (⟨(W.map A.subtype).stepCurve H ℓ, (W.map A.subtype).stepSubgroup H ℓ⟩ :
      Σ V : WeierstrassCurve K, AddSubgroup V.toAffine.Point) = ⟨Vq, Hq⟩
  σk : (⟨(W.map (residue A)).stepCurve (H.map (reduceHom hΔ)) ℓ,
        (W.map (residue A)).stepSubgroup (H.map (reduceHom hΔ)) ℓ⟩ :
      Σ V : WeierstrassCurve (ResidueField A), AddSubgroup V.toAffine.Point) = ⟨Vr, Hr⟩
  hΔ' : (W'.map (residue A)).Δ ≠ 0
  hHq : Hq ∈ CycSub Vq.toAffine.Point M
  hHr : Hr ∈ CycSub Vr.toAffine.Point M
  key : ∀ P ∈ Hq, P ≠ 0 → ∃ (X Y : K) (h₁ : Vq.toAffine.Nonsingular X Y) (hX : X ∈ A),
    P = .some X Y h₁ ∧ ∃ U ∈ Hr, ∃ (Ybar : ResidueField A)
      (h₂ : Vr.toAffine.Nonsingular (residue A ⟨X, hX⟩) Ybar), U = .some (residue A ⟨X, hX⟩) Ybar h₂

theorem step_of_stepData {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0)
    {H : AddSubgroup (W.map A.subtype).toAffine.Point} {N M : ℕ} (hN2 : 2 ≤ N)
    (hNM : N / N.minFac = M) (hM : (M : ResidueField A) ≠ 0) (hM0 : M ≠ 0)
    (D : StepData W hΔ H N.minFac M) (IH : Claim A M) :
    ∃ hmem : (W.map A.subtype).cyclicQuotientJ H N ∈ A,
      residue A ⟨_, hmem⟩ = (W.map (residue A)).cyclicQuotientJ (H.map (reduceHom hΔ)) N := by

  set H' : AddSubgroup (D.W'.map A.subtype).toAffine.Point :=
    D.Hq.map (castHom D.eK.symm).toAddMonoidHom with hH'def
  have hH' : H' ∈ CycSub _ M := map_equiv_mem_cycSub _ D.hHq
  have hH'tor : ∀ P ∈ H', M • P = 0 := fun P hP => nsmul_eq_zero_of_mem_cycSub hH' hP

  obtain ⟨hmem', hres'⟩ := IH D.W' D.hΔ' H' hH'

  have hσ' : (⟨D.W'.map A.subtype, H'⟩ : Σ V : WeierstrassCurve K, AddSubgroup V.toAffine.Point) =
      ⟨D.Vq, D.Hq⟩ := sigma_castHom D.eK.symm D.Hq
  have hgen : (W.map A.subtype).cyclicQuotientJ H N = (D.W'.map A.subtype).cyclicQuotientJ H' M := by
    rw [cyclicQuotientJ_eq_of_two_le _ H hN2, hNM, cyclicQuotientJ_congr D.σK M,
      cyclicQuotientJ_congr hσ' M]
  refine ⟨hgen ▸ hmem', ?_⟩
  have e1 : residue A ⟨(W.map A.subtype).cyclicQuotientJ H N, hgen ▸ hmem'⟩ =
      residue A ⟨(D.W'.map A.subtype).cyclicQuotientJ H' M, hmem'⟩ :=
    congrArg (residue A) (Subtype.ext hgen)
  rw [e1, hres', cyclicQuotientJ_eq_of_two_le _ (H.map (reduceHom hΔ)) hN2, hNM,
    cyclicQuotientJ_congr D.σk M]

  set R₂ : AddSubgroup (D.W'.map (residue A)).toAffine.Point :=
    D.Hr.map (castHom D.ek.symm).toAddMonoidHom with hR₂def
  have hR₂ : R₂ ∈ CycSub _ M := map_equiv_mem_cycSub _ D.hHr
  have hσ₂ : (⟨D.W'.map (residue A), R₂⟩ :
      Σ V : WeierstrassCurve (ResidueField A), AddSubgroup V.toAffine.Point) = ⟨D.Vr, D.Hr⟩ :=
    sigma_castHom D.ek.symm D.Hr
  suffices hR : H'.map (reduceHom D.hΔ') = R₂ by
    rw [hR]; exact cyclicQuotientJ_congr hσ₂ M

  have hle : H'.map (reduceHom D.hΔ') ≤ R₂ := by
    rintro T ⟨P', hP', rfl⟩
    obtain ⟨P, hP, rfl⟩ := hP'
    by_cases hP0 : P = 0
    · subst hP0
      simp only [map_zero]
      exact R₂.zero_mem
    obtain ⟨X, Y, h₁, hX, rfl, U, hU, Ybar, h₂, hUeq⟩ := D.key P hP hP0
    change reduceHom D.hΔ' (castHom D.eK.symm (Affine.Point.some X Y h₁)) ∈ R₂
    rw [castHom_some, reduceHom_some D.hΔ' _ hX]

    have hU' : castHom D.ek.symm U ∈ R₂ := ⟨U, hU, rfl⟩
    rw [hUeq, castHom_some] at hU'
    have hns₁ : (D.W'.map A.subtype).toAffine.Nonsingular X Y := D.eK.symm ▸ h₁
    have hY : Y ∈ A := Affine.Y_mem_of_X_mem D.W' hns₁.1 hX
    have hnsT : (D.W'.map (residue A)).toAffine.Nonsingular (residue A ⟨X, hX⟩) (residue A ⟨Y, hY⟩) :=
      Affine.nonsingular_residue D.W' D.hΔ' (x := ⟨X, hX⟩) (y := ⟨Y, hY⟩) hns₁.1
    rcases eq_or_eq_neg_of_fst_eq (D.ek.symm ▸ h₂) hnsT with h | h
    · rw [h]; exact hU'
    · rw [h]; exact R₂.neg_mem hU'

  haveI : Finite R₂ := finite_of_mem_cycSub hM0 hR₂
  refine AddSubgroup.eq_of_le_of_card_ge hle ?_
  rw [hR₂.2, ← SetLike.coe_sort_coe (H'.map _), AddSubgroup.coe_map,
    Nat.card_image_of_injOn (injOn_reduceHom D.hΔ' hM hH'tor), SetLike.coe_sort_coe, hH'.2]

end Step

section OddStep

variable {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K] {A : ValuationSubring K}
  [DecidableEq (ResidueField A)] [IsAlgClosed (ResidueField A)]

theorem nonempty_stepData_odd {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0)
    {H : AddSubgroup (W.map A.subtype).toAffine.Point} {N M : ℕ} (hN0 : N ≠ 0)
    (hN : (N : ResidueField A) ≠ 0) (hH : H ∈ CycSub _ N)
    (hNM : N = N.minFac * M) (hℓ : N.minFac.Prime) (hℓ2 : N.minFac ≠ 2) :
    Nonempty (StepData W hΔ H N.minFac M) := by
  set ℓ := N.minFac with hℓdef
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : (W.map A.subtype).IsElliptic := isElliptic_generic hΔ
  haveI : (W.map (residue A)).IsElliptic := isElliptic_special hΔ
  haveI := hH.1
  haveI : Finite H := finite_of_mem_cycSub hN0 hH
  have hHtor : ∀ P ∈ H, N • P = 0 := fun P hP => nsmul_eq_zero_of_mem_cycSub hH hP

  have hℓk : (ℓ : ResidueField A) ≠ 0 := fun h => hN (by rw [hNM, Nat.cast_mul, h, zero_mul])
  have hℓK : (ℓ : K) ≠ 0 := natCast_ne_zero_of_residue hℓk
  have hℓodd : Odd ℓ := hℓ.odd_of_ne_two hℓ2
  have hℓn : 2 * (ℓ / 2) + 1 = ℓ := Nat.two_mul_div_two_add_one_of_odd hℓodd
  have hmk : ((2 * (ℓ / 2) + 1 : ℕ) : ResidueField A) ≠ 0 := by rw [hℓn]; exact hℓk

  obtain ⟨Q, hQH, hQ⟩ := exists_mem_addOrderOf_eq hN0 hH hℓ (by rw [hNM]; exact dvd_mul_right ℓ M)
  have hQn : addOrderOf Q = 2 * (ℓ / 2) + 1 := by rw [hℓn, hQ]

  obtain ⟨φ, hker, hφ⟩ := (W.map A.subtype).exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed hℓ hℓ2 hℓK Q hQ
  have σK := (W.map A.subtype).stepCurve_stepSubgroup_eq_of_prime_ne_two hℓ hℓ2 H Q hQH hQ φ hker hφ

  have hQb : addOrderOf (reduceHom hΔ Q) = ℓ := addOrderOf_reduceHom_of_natCast_ne_zero hΔ hℓk hQ
  have hQbn : addOrderOf (reduceHom hΔ Q) = 2 * (ℓ / 2) + 1 := by rw [hℓn, hQb]
  have hHb : (H.map (reduceHom hΔ)) ∈ CycSub _ N := map_mem_cycSub_of_injOn (reduceHom hΔ) hH (injOn_reduceHom hΔ hN hHtor)
  haveI := hHb.1
  haveI : Finite (H.map (reduceHom hΔ)) := finite_of_mem_cycSub hN0 hHb
  have hQHb : (reduceHom hΔ Q) ∈ (H.map (reduceHom hΔ)) := ⟨Q, hQH, rfl⟩
  obtain ⟨φb, hkerb, hφb⟩ :=
    (W.map (residue A)).exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed hℓ hℓ2 hℓk (reduceHom hΔ Q) hQb
  have σk := (W.map (residue A)).stepCurve_stepSubgroup_eq_of_prime_ne_two hℓ hℓ2 (H.map (reduceHom hΔ)) (reduceHom hΔ Q) hQHb hQb φb hkerb hφb

  obtain ⟨W', eK, ek⟩ := W.exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom A hΔ
    hℓk Q hQ (n := ℓ / 2) (Nat.div_lt_self hℓ.pos one_lt_two)

  have hΔ' : (W'.map (residue A)).Δ ≠ 0 := by
    rw [ek]
    have hid := (W.map (residue A)).veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow (reduceHom hΔ Q) hQbn
    intro h0
    rw [h0, zero_mul] at hid
    exact pow_ne_zero _ (W.map (residue A)).Δ'.ne_zero (by rw [coe_Δ']; exact hid.symm)

  have hkerle : φ.ker ≤ H := by rw [hker]; exact AddSubgroup.zmultiples_le.2 hQH
  have hkerble : φb.ker ≤ (H.map (reduceHom hΔ)) := by rw [hkerb]; exact AddSubgroup.zmultiples_le.2 hQHb
  have hHq : H.map φ ∈ CycSub _ M :=
    map_mem_cycSub φ hℓ.ne_zero (hNM ▸ hH) hkerle (by rw [hker, Nat.card_zmultiples, hQ])
  have hHr : (H.map (reduceHom hΔ)).map φb ∈ CycSub _ M :=
    map_mem_cycSub φb hℓ.ne_zero (hNM ▸ hHb) hkerble (by rw [hkerb, Nat.card_zmultiples, hQb])
  refine ⟨{
    Vq := (W.map A.subtype).veluQuotient ((W.map A.subtype).oddOrderSummingSet Q (ℓ / 2))
    Hq := H.map φ
    Vr := (W.map (residue A)).veluQuotient ((W.map (residue A)).oddOrderSummingSet (reduceHom hΔ Q) (ℓ / 2))
    Hr := (H.map (reduceHom hΔ)).map φb
    W' := W'
    eK := eK
    ek := ek
    σK := σK
    σk := σk
    hΔ' := hΔ'
    hHq := hHq
    hHr := hHr
    key := ?_ }⟩

  rintro P₁ ⟨P, hPH, rfl⟩ hP0
  have hPker : P ∉ AddSubgroup.zmultiples Q := by
    intro h; apply hP0
    have : P ∈ φ.ker := hker ▸ h
    exact this
  have hPne : P ≠ 0 := fun h => hPker (h ▸ AddSubgroup.zero_mem _)
  obtain ⟨x, y, hxy, rfl⟩ := exists_eq_some_of_ne_zero hPne
  obtain ⟨h', hφP⟩ := hφ x y hxy hPker
  have hx : x ∈ A := X_mem hN hHtor hPH

  have hx' : ∀ P' ∈ (W.map (residue A)).oddOrderSummingSet (reduceHom hΔ Q) (ℓ / 2), P'.1 ≠ residue A ⟨x, hx⟩ := by
    intro P' hP' hP'x
    obtain ⟨k, hk1, hk2, hkP'⟩ := ((W.map (residue A)).mem_oddOrderSummingSet).1 hP'

    have hkQH : k • Q ∈ H := H.nsmul_mem hQH k
    have hkQ0 : k • Q ≠ 0 := nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)
    obtain ⟨xk, yk, hk, hkQ⟩ := exists_eq_some_of_ne_zero hkQ0
    have hkQH' : Affine.Point.some xk yk hk ∈ H := hkQ ▸ hkQH
    have hxk : xk ∈ A := X_mem hN hHtor hkQH'
    have hred : k • (reduceHom hΔ Q) = .some (residue A ⟨xk, hxk⟩) (residue A ⟨yk, Affine.Y_mem_of_X_mem W hk.1 hxk⟩)
        (Affine.nonsingular_residue W hΔ hk.1) := by
      rw [← map_nsmul, hkQ]; exact reduceHom_some hΔ hk hxk
    rw [hred, Affine.Point.coordsOrZero_some] at hkP'
    have hxx : residue A ⟨x, hx⟩ = residue A ⟨xk, hxk⟩ := by rw [← hP'x, ← hkP']
    rcases eq_or_eq_neg_of_residue_X_eq hΔ hN hHtor hPH hkQH' hxx with h | h
    · exact hPker (h ▸ hkQ ▸ ⟨k, natCast_zsmul Q k⟩)
    · exact hPker (h ▸ hkQ ▸ (AddSubgroup.zmultiples Q).neg_mem ⟨k, natCast_zsmul Q k⟩)
  obtain ⟨hX, hXres⟩ :=
    veluX_mem_and_residue_veluX_eq_of_forall_fst_ne_residue hΔ hmk Q hQn hQbn hx hx'
  refine ⟨(W.map A.subtype).veluX ((W.map A.subtype).oddOrderSummingSet Q (ℓ / 2)) x, (W.map A.subtype).veluY ((W.map A.subtype).oddOrderSummingSet Q (ℓ / 2)) x y, h', hX, hφP, ?_⟩

  have hrP : (reduceHom hΔ) (.some x y hxy) = .some (residue A ⟨x, hx⟩)
      (residue A ⟨y, Affine.Y_mem_of_X_mem W hxy.1 hx⟩) (Affine.nonsingular_residue W hΔ hxy.1) :=
    reduceHom_some hΔ hxy hx
  have hrPker : (reduceHom hΔ) (.some x y hxy) ∉ AddSubgroup.zmultiples (reduceHom hΔ Q) := by
    intro h
    rw [← AddMonoidHom.map_zmultiples] at h
    exact hPker (mem_of_reduceHom_mem_map hΔ hN hHtor (AddSubgroup.zmultiples_le.2 hQH) hPH h)
  rw [hrP] at hrPker
  obtain ⟨h₃, hφbP⟩ := hφb _ _ _ hrPker
  refine ⟨φb ((reduceHom hΔ) (.some x y hxy)), ⟨_, ⟨_, hPH, rfl⟩, rfl⟩, (W.map (residue A)).veluY ((W.map (residue A)).oddOrderSummingSet (reduceHom hΔ Q) (ℓ / 2)) (residue A ⟨x, hx⟩)
    (residue A ⟨y, Affine.Y_mem_of_X_mem W hxy.1 hx⟩), hXres ▸ h₃, ?_⟩
  rw [hrP, hφbP]
  exact some_congr hXres.symm rfl _ _

end OddStep

section TwoStep

variable {K : Type u} [Field K] [DecidableEq K] {A : ValuationSubring K}
  [DecidableEq (ResidueField A)]

theorem map_veluGx {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (f : R →+* S)
    (a b : R) : (W.map f).veluGx (f a) (f b) = f (W.veluGx a b) := by
  simp [veluGx, map_ofNat]

theorem map_veluGy {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (f : R →+* S)
    (a b : R) : (W.map f).veluGy (f a) (f b) = f (W.veluGy a b) := by
  simp [veluGy, map_ofNat]

theorem map_veluQuotient2 {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)
    (f : R →+* S) (a b : R) : (W.veluQuotient2 a b).map f = (W.map f).veluQuotient2 (f a) (f b) := by
  ext <;> simp [veluQuotient2, veluGx, map_b₂, map_ofNat]

theorem veluGy_eq_zero_of_two_nsmul {F : Type*} [Field F] [DecidableEq F] {V : WeierstrassCurve F}
    {x₀ y₀ : F} {h : V.toAffine.Nonsingular x₀ y₀}
    (h2 : (2 : ℕ) • (Affine.Point.some x₀ y₀ h : V.toAffine.Point) = 0) : V.veluGy x₀ y₀ = 0 := by
  rw [two_nsmul, ← eq_neg_iff_add_eq_zero, Affine.Point.neg_some] at h2
  exact V.veluGy_eq_zero_of_negY_eq (Affine.Point.some.inj h2).2.symm

theorem mem_ker_veluPointMap2 {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F)
    [E.IsElliptic] (h2 : (2 : F) ≠ 0) {x₀ y₀ : F}
    (hQ : E.toAffine.Equation x₀ y₀) (hgy : E.veluGy x₀ y₀ = 0) (hΔ : (E.veluQuotient2 x₀ y₀).Δ ≠ 0)
    (φ : E.toAffine.Point →+ (E.veluQuotient2 x₀ y₀).toAffine.Point)
    (hφ : ⇑φ = veluPointMap2 h2 hQ hgy hΔ) (P : E.toAffine.Point) :
    P ∈ φ.ker ↔ P = 0 ∨ P = .some x₀ y₀ ((E.toAffine.equation_iff_nonsingular).1 hQ) := by
  rw [AddMonoidHom.mem_ker, hφ]
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
  · by_cases hx : x = x₀
    · rw [veluPointMap2_some_of_eq _ _ _ _ _ hx]
      refine ⟨fun _ => ?_, fun _ => rfl⟩
      right
      subst hx
      have hneg : E.toAffine.negY x y₀ = y₀ := by
        rw [Affine.negY]; rw [veluGy] at hgy; linear_combination hgy
      rcases Affine.Y_eq_of_X_eq h.1 hQ rfl with hy | hy
      · subst hy; rfl
      · rw [hneg] at hy; subst hy; rfl
    · rw [veluPointMap2_some_of_ne _ _ _ _ _ hx]
      constructor
      · intro h0; exact absurd h0 (Affine.Point.some_ne_zero _)
      · rintro (h0 | hP)
        · exact absurd h0 (Affine.Point.some_ne_zero _)
        · exact absurd (Affine.Point.some.inj hP).1 hx

theorem ker_eq_zmultiples_of_veluPointMap2 {F : Type*} [Field F] [DecidableEq F]
    (E : WeierstrassCurve F) [E.IsElliptic] (h2 : (2 : F) ≠ 0) {x₀ y₀ : F} (hns : E.toAffine.Nonsingular x₀ y₀)
    (hgy : E.veluGy x₀ y₀ = 0) (hΔ : (E.veluQuotient2 x₀ y₀).Δ ≠ 0)
    (φ : E.toAffine.Point →+ (E.veluQuotient2 x₀ y₀).toAffine.Point)
    (hφ : ⇑φ = veluPointMap2 h2 hns.1 hgy hΔ) :
    φ.ker = AddSubgroup.zmultiples (Affine.Point.some x₀ y₀ hns) := by
  have h2Q : (2 : ℕ) • (Affine.Point.some x₀ y₀ hns : E.toAffine.Point) = 0 := by
    rw [two_nsmul, ← eq_neg_iff_add_eq_zero, Affine.Point.neg_some]
    congr 1
    rw [Affine.negY]; rw [veluGy] at hgy; linear_combination -hgy
  have hord : addOrderOf (Affine.Point.some x₀ y₀ hns : E.toAffine.Point) = 2 :=
    addOrderOf_eq_prime_iff.2 ⟨h2Q, Affine.Point.some_ne_zero _⟩
  ext P
  rw [mem_ker_veluPointMap2 E h2 hns.1 hgy hΔ φ hφ]
  constructor
  · rintro (rfl | rfl)
    · exact AddSubgroup.zero_mem _
    · exact AddSubgroup.mem_zmultiples _
  · intro hP
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hP
    have hk : (k % 2) • (Affine.Point.some x₀ y₀ hns : E.toAffine.Point) =
        k • Affine.Point.some x₀ y₀ hns := by
      have := mod_addOrderOf_zsmul (Affine.Point.some x₀ y₀ hns : E.toAffine.Point) k
      rwa [hord, Nat.cast_ofNat] at this
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left; rw [← hk, h, zero_smul]
    · right; rw [← hk, h, one_smul]

theorem velu2X_mem_and_residue_eq {W : WeierstrassCurve A} {x₀ y₀ x : K} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hx : x ∈ A) (hxx : residue A ⟨x, hx⟩ ≠ residue A ⟨x₀, hx₀⟩) :
    ∃ hmem : (W.map A.subtype).velu2X x₀ y₀ x ∈ A,
      residue A ⟨_, hmem⟩ = (W.map (residue A)).velu2X (residue A ⟨x₀, hx₀⟩) (residue A ⟨y₀, hy₀⟩)
        (residue A ⟨x, hx⟩) := by
  have hg : (W.map A.subtype).veluGx x₀ y₀ = ((W.veluGx ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩ : A) : K) :=
    map_veluGx W A.subtype ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩
  have hgA : (W.map A.subtype).veluGx x₀ y₀ ∈ A := by rw [hg]; exact SetLike.coe_mem _
  have hd : x - x₀ ∈ A := sub_mem hx hx₀
  have hd' : x - x₀ ∉ A.nonunits := by
    intro h
    apply hxx
    exact (A.residue_eq_residue_iff_sub_mem_nonunits hx hx₀).2 h
  have hq : (W.map A.subtype).veluGx x₀ y₀ / (x - x₀) ∈ A := A.div_mem_of_mem_of_notMem_nonunits hgA hd'
  refine ⟨add_mem hx hq, ?_⟩
  have e1 : residue A ⟨(W.map A.subtype).velu2X x₀ y₀ x, add_mem hx hq⟩ =
      residue A (⟨x, hx⟩ + ⟨_, hq⟩) := rfl
  have e2 : (⟨x - x₀, hd⟩ : A) = ⟨x, hx⟩ - ⟨x₀, hx₀⟩ := rfl
  rw [e1, map_add, A.residue_div hgA hd hd' hq, velu2X, A.residue_eq_of_coe_eq hgA hg,
    ← map_veluGx W (residue A), e2, map_sub]

variable [IsAlgClosed K] [IsAlgClosed (ResidueField A)]

theorem nonempty_stepData_two {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0)
    {H : AddSubgroup (W.map A.subtype).toAffine.Point} {N M : ℕ} (hN0 : N ≠ 0)
    (hN : (N : ResidueField A) ≠ 0) (hH : H ∈ CycSub _ N)
    (hNM : N = N.minFac * M) (hℓ2 : N.minFac = 2) :
    Nonempty (StepData W hΔ H N.minFac M) := by
  rw [hℓ2] at hNM ⊢
  haveI : (W.map A.subtype).IsElliptic := isElliptic_generic hΔ
  haveI : (W.map (residue A)).IsElliptic := isElliptic_special hΔ
  haveI := hH.1
  haveI : Finite H := finite_of_mem_cycSub hN0 hH
  have hHtor : ∀ P ∈ H, N • P = 0 := fun P hP => nsmul_eq_zero_of_mem_cycSub hH hP
  have h2k : (2 : ResidueField A) ≠ 0 := fun h => hN (by
    rw [hNM, Nat.cast_mul, Nat.cast_ofNat, h, zero_mul])
  have h2K : (2 : K) ≠ 0 := by exact_mod_cast natCast_ne_zero_of_residue (n := 2) (by exact_mod_cast h2k)

  obtain ⟨Q, hQH, hQ⟩ := exists_mem_addOrderOf_eq hN0 hH Nat.prime_two (by rw [hNM]; exact dvd_mul_right 2 M)
  have hQ0 : Q ≠ 0 := fun h => by rw [h, addOrderOf_zero] at hQ; exact absurd hQ (by norm_num)
  obtain ⟨x₀, y₀, hns, rfl⟩ := exists_eq_some_of_ne_zero hQ0
  have h2Q : (2 : ℕ) • (Affine.Point.some x₀ y₀ hns : (W.map A.subtype).toAffine.Point) = 0 := by
    rw [← hQ]; exact addOrderOf_nsmul_eq_zero _
  have hgy : (W.map A.subtype).veluGy x₀ y₀ = 0 := veluGy_eq_zero_of_two_nsmul h2Q
  have hΔ₂ : ((W.map A.subtype).veluQuotient2 x₀ y₀).Δ ≠ 0 := veluQuotient2_Delta_ne_zero (W.map A.subtype).Δ'.ne_zero hns.1 hgy
  obtain ⟨φ, hφ⟩ := (W.map A.subtype).exists_addMonoidHom_coe_eq_veluPointMap2 h2K hns.1 hgy hΔ₂
  have hker := ker_eq_zmultiples_of_veluPointMap2 (W.map A.subtype) h2K hns hgy hΔ₂ φ hφ
  have σK := (W.map A.subtype).stepCurve_stepSubgroup_two_eq h2K H hns hQH hgy hΔ₂ φ hφ

  have hx₀ : x₀ ∈ A := X_mem hN hHtor hQH
  have hy₀ : y₀ ∈ A := Affine.Y_mem_of_X_mem W hns.1 hx₀

  have hHb : (H.map (reduceHom hΔ)) ∈ CycSub _ N := map_mem_cycSub_of_injOn (reduceHom hΔ) hH (injOn_reduceHom hΔ hN hHtor)
  haveI := hHb.1
  haveI : Finite (H.map (reduceHom hΔ)) := finite_of_mem_cycSub hN0 hHb
  have hnsb : (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x₀, hx₀⟩) (residue A ⟨y₀, hy₀⟩) :=
    Affine.nonsingular_residue W hΔ hns.1
  have hrQ : (reduceHom hΔ) (.some x₀ y₀ hns) = .some (residue A ⟨x₀, hx₀⟩) (residue A ⟨y₀, hy₀⟩) hnsb :=
    reduceHom_some hΔ hns hx₀
  have hQHb : Affine.Point.some (residue A ⟨x₀, hx₀⟩) (residue A ⟨y₀, hy₀⟩) hnsb ∈ (H.map (reduceHom hΔ)) :=
    ⟨_, hQH, hrQ⟩
  have h2Qb : (2 : ℕ) • (Affine.Point.some (residue A ⟨x₀, hx₀⟩) (residue A ⟨y₀, hy₀⟩) hnsb :
      (W.map (residue A)).toAffine.Point) = 0 := by
    rw [← hrQ, ← map_nsmul, h2Q, map_zero]
  have hgyb : (W.map (residue A)).veluGy (residue A ⟨x₀, hx₀⟩) (residue A ⟨y₀, hy₀⟩) = 0 := veluGy_eq_zero_of_two_nsmul h2Qb
  have hΔ₂b : ((W.map (residue A)).veluQuotient2 (residue A ⟨x₀, hx₀⟩) (residue A ⟨y₀, hy₀⟩)).Δ ≠ 0 :=
    veluQuotient2_Delta_ne_zero (W.map (residue A)).Δ'.ne_zero hnsb.1 hgyb
  obtain ⟨φb, hφb⟩ := (W.map (residue A)).exists_addMonoidHom_coe_eq_veluPointMap2 h2k hnsb.1 hgyb hΔ₂b
  have hkerb := ker_eq_zmultiples_of_veluPointMap2 (W.map (residue A)) h2k hnsb hgyb hΔ₂b φb hφb
  have σk := (W.map (residue A)).stepCurve_stepSubgroup_two_eq h2k (H.map (reduceHom hΔ)) hnsb hQHb hgyb hΔ₂b φb hφb

  let W' : WeierstrassCurve A := W.veluQuotient2 ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩
  have eK : W'.map A.subtype = (W.map A.subtype).veluQuotient2 x₀ y₀ := map_veluQuotient2 W A.subtype _ _
  have ek : W'.map (residue A) = (W.map (residue A)).veluQuotient2 (residue A ⟨x₀, hx₀⟩) (residue A ⟨y₀, hy₀⟩) :=
    map_veluQuotient2 W (residue A) _ _
  have hΔ' : (W'.map (residue A)).Δ ≠ 0 := by rw [ek]; exact hΔ₂b

  have hkerle : φ.ker ≤ H := by rw [hker]; exact AddSubgroup.zmultiples_le.2 hQH
  have hkerble : φb.ker ≤ (H.map (reduceHom hΔ)) := by rw [hkerb]; exact AddSubgroup.zmultiples_le.2 hQHb
  have hQb : addOrderOf (Affine.Point.some (residue A ⟨x₀, hx₀⟩) (residue A ⟨y₀, hy₀⟩) hnsb :
      (W.map (residue A)).toAffine.Point) = 2 := by
    rw [← hrQ]; exact addOrderOf_reduceHom_of_natCast_ne_zero hΔ (by exact_mod_cast h2k) hQ
  have hHq : H.map φ ∈ CycSub _ M :=
    map_mem_cycSub φ two_ne_zero (hNM ▸ hH) hkerle (by rw [hker, Nat.card_zmultiples, hQ])
  have hHr : (H.map (reduceHom hΔ)).map φb ∈ CycSub _ M :=
    map_mem_cycSub φb two_ne_zero (hNM ▸ hHb) hkerble (by rw [hkerb, Nat.card_zmultiples, hQb])
  refine ⟨{
    Vq := (W.map A.subtype).veluQuotient2 x₀ y₀
    Hq := H.map φ
    Vr := (W.map (residue A)).veluQuotient2 (residue A ⟨x₀, hx₀⟩) (residue A ⟨y₀, hy₀⟩)
    Hr := (H.map (reduceHom hΔ)).map φb
    W' := W'
    eK := eK
    ek := ek
    σK := σK
    σk := σk
    hΔ' := hΔ'
    hHq := hHq
    hHr := hHr
    key := ?_ }⟩

  rintro P₁ ⟨P, hPH, rfl⟩ hP0
  have hPker : P ∉ φ.ker := fun h => hP0 h
  have hPne : P ≠ 0 := fun h => hPker (h ▸ φ.ker.zero_mem)
  obtain ⟨x, y, hxy, rfl⟩ := exists_eq_some_of_ne_zero hPne
  have hx : x ∈ A := X_mem hN hHtor hPH

  have hxx : residue A ⟨x, hx⟩ ≠ residue A ⟨x₀, hx₀⟩ := by
    intro h
    apply hPker
    rw [hker]
    rcases eq_or_eq_neg_of_residue_X_eq hΔ hN hHtor hPH hQH h with h' | h'
    · rw [h']; exact AddSubgroup.mem_zmultiples _
    · rw [h']; exact (AddSubgroup.zmultiples _).neg_mem (AddSubgroup.mem_zmultiples _)
  have hxne : x ≠ x₀ := fun h => hxx (by subst h; rfl)
  have hφP : φ (.some x y hxy) = .some ((W.map A.subtype).velu2X x₀ y₀ x) ((W.map A.subtype).velu2Y x₀ y₀ x y)
      (velu2_map_nonsingular h2K hxy.1 hns.1 hgy hxne hΔ₂) := by
    rw [hφ]; exact veluPointMap2_some_of_ne h2K hns.1 hgy hΔ₂ hxy hxne
  obtain ⟨hX, hXres⟩ := velu2X_mem_and_residue_eq (W := W) (y₀ := y₀) hx₀ hy₀ hx hxx
  refine ⟨(W.map A.subtype).velu2X x₀ y₀ x, (W.map A.subtype).velu2Y x₀ y₀ x y, _, hX, hφP, ?_⟩

  have hrP : (reduceHom hΔ) (.some x y hxy) = .some (residue A ⟨x, hx⟩)
      (residue A ⟨y, Affine.Y_mem_of_X_mem W hxy.1 hx⟩) (Affine.nonsingular_residue W hΔ hxy.1) :=
    reduceHom_some hΔ hxy hx
  have hφbP : φb ((reduceHom hΔ) (.some x y hxy)) = .some ((W.map (residue A)).velu2X (residue A ⟨x₀, hx₀⟩) (residue A ⟨y₀, hy₀⟩)
      (residue A ⟨x, hx⟩)) _ (velu2_map_nonsingular h2k (Affine.nonsingular_residue W hΔ (x := ⟨x, hx⟩)
        (y := ⟨y, Affine.Y_mem_of_X_mem W hxy.1 hx⟩) hxy.1).1 hnsb.1 hgyb hxx hΔ₂b) := by
    rw [hrP, hφb]; exact veluPointMap2_some_of_ne h2k hnsb.1 hgyb hΔ₂b _ hxx
  refine ⟨φb ((reduceHom hΔ) (.some x y hxy)), ⟨_, ⟨_, hPH, rfl⟩, rfl⟩, _, hXres ▸ (velu2_map_nonsingular h2k
    (Affine.nonsingular_residue W hΔ (x := ⟨x, hx⟩) (y := ⟨y, Affine.Y_mem_of_X_mem W hxy.1 hx⟩) hxy.1).1
    hnsb.1 hgyb hxx hΔ₂b), ?_⟩
  rw [hφbP]
  exact some_congr hXres.symm rfl _ _

end TwoStep

section Main

variable {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K] {A : ValuationSubring K}
  [DecidableEq (ResidueField A)] [IsAlgClosed (ResidueField A)]

theorem claim_one : Claim A 1 := by
  intro W hΔ H hH
  have hc : (W.map A.subtype).c₄ = ((W.c₄ : A) : K) := map_c₄ W A.subtype
  have hd : (W.map A.subtype).Δ = ((W.Δ : A) : K) := map_Δ W A.subtype
  have hcA : (W.map A.subtype).c₄ ^ 3 ∈ A := by rw [hc]; exact pow_mem (SetLike.coe_mem _) 3
  have hdA : (W.map A.subtype).Δ ∈ A := by rw [hd]; exact SetLike.coe_mem _
  have hdu : (W.map A.subtype).Δ ∉ A.nonunits := by rw [hd]; exact coe_Δ_notMem_nonunits hΔ
  have hmem : (W.map A.subtype).c₄ ^ 3 / (W.map A.subtype).Δ ∈ A :=
    A.div_mem_of_mem_of_notMem_nonunits hcA hdu
  have hj : (W.map A.subtype).cyclicQuotientJ H 1 = (W.map A.subtype).c₄ ^ 3 / (W.map A.subtype).Δ :=
    cyclicQuotientJ_one _ H
  have hmem' : (W.map A.subtype).cyclicQuotientJ H 1 ∈ A := by rw [hj]; exact hmem
  refine ⟨hmem', ?_⟩
  have e1 : residue A ⟨(W.map A.subtype).cyclicQuotientJ H 1, hmem'⟩ = residue A ⟨_, hmem⟩ :=
    congrArg (residue A) (Subtype.ext hj)
  rw [e1, A.residue_div hcA hdA hdu hmem, cyclicQuotientJ_one,
    A.residue_eq_of_coe_eq hcA (v := W.c₄ ^ 3) (by rw [hc]; push_cast; rfl),
    A.residue_eq_of_coe_eq hdA (v := W.Δ) hd, map_pow, map_c₄, map_Δ]

theorem claim_all : ∀ N : ℕ, N ≠ 0 → (N : ResidueField A) ≠ 0 → Claim A N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IHN =>
  intro hN0 hN W hΔ H hH
  by_cases hN1 : N = 1
  · subst hN1; exact claim_one W hΔ H hH
  have hN2 : 2 ≤ N := by omega
  set ℓ := N.minFac with hℓdef
  have hℓ : ℓ.Prime := Nat.minFac_prime hN1
  set M := N / ℓ with hMdef
  have hNM : N = ℓ * M := (Nat.mul_div_cancel' (Nat.minFac_dvd N)).symm
  have hM0 : M ≠ 0 := fun h => hN0 (by rw [hNM, h, mul_zero])
  have hMk : (M : ResidueField A) ≠ 0 := fun h => hN (by rw [hNM, Nat.cast_mul, h, mul_zero])
  have hMlt : M < N := by
    rw [hMdef]; exact Nat.div_lt_self (by omega) hℓ.one_lt
  have IH : Claim A M := IHN M hMlt hM0 hMk
  obtain ⟨D⟩ : Nonempty (StepData W hΔ H ℓ M) := by
    by_cases hℓ2 : ℓ = 2
    · exact nonempty_stepData_two hΔ hN0 hN hH hNM hℓ2
    · exact nonempty_stepData_odd hΔ hN0 hN hH hNM hℓ hℓ2
  exact step_of_stepData hΔ hN2 hMdef.symm hMk hM0 D IH

end Main

end CQJReduce
end WeierstrassCurve

theorem solution
    {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K] {A : ValuationSubring K}
    [DecidableEq (ResidueField A)] [IsAlgClosed (ResidueField A)]
    {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0)
    {N : ℕ} [NeZero N] (hN : (N : ResidueField A) ≠ 0)
    (H : AddSubgroup (W.map A.subtype).toAffine.Point) (hH : IsAddCyclic H) (hcard : Nat.card H = N) :
    ∃ hmem : (W.map A.subtype).cyclicQuotientJ H N ∈ A,
      residue A ⟨_, hmem⟩ = (W.map (residue A)).cyclicQuotientJ (H.map (reduceHom hΔ)) N :=
  WeierstrassCurve.CQJReduce.claim_all N (NeZero.ne N) hN W hΔ H ⟨hH, hcard⟩

end S_WeierstrassCurve_residue_cyclicQuotientJ_eq_cyclicQuotientJ_map_reduceHom
end P2MW
export P2MW.S_WeierstrassCurve_residue_cyclicQuotientJ_eq_cyclicQuotientJ_map_reduceHom (solution)
