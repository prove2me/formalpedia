-- Prove2me | solution 1 for ValuationSubring.exists_transcendental_forall_over_gauss_iff_mem_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/915b600e-fa70-5ceb-a1cc-951bfc8f65fb

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ValuationSubring_inv_mem_and_chartAlg_le_and_over_gauss_and_isDiscreteValuationRing_of_forall_isUnit_polynomialEval2
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_mem_minimalPrimes_or_isMaximal_of_mem_chartAlgFin
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
import Theorems.Thm_Ideal_exists_isMaximal_forall_mem_minimalPrimes_le_imp_eq_of_finiteType
import Theorems.Thm_IsIntegrallyClosed_exists_not_mem_and_mul_mem_span_singleton_of_forall_mem_minimalPrimes_not_mem
import Theorems.Thm_HenselianLocalRing_exists_ideal_moduleFinite_quotient_of_forall_isPrime_imp_eq_of_isDiscreteValuationRing
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_forall_over_gauss_iff_exists_forall_mem_iff_of_mul_pow_isUnit_of_forall_mem_localization
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_forall_mem_localization_chartAlg_and_mul_pow_jChartFin_isUnit_of_branchData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_transcendental_forall_over_gauss_iff_mem_of_henselianLocalRing
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply"
p2m_attr_erase "simp" "AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

universe u

open IsLocalRing AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

namespace PenC4

theorem not_isUnit_unif {R : Type u} [CommRing R] [IsLocalRing R] (ϖ : R)
    (hϖ : maximalIdeal R = Ideal.span {ϖ}) : ¬ IsUnit ϖ := by
  have : ϖ ∈ maximalIdeal R := by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ
  exact (IsLocalRing.mem_maximalIdeal _).mp this

theorem not_C_dvd {R : Type u} [CommRing R] [IsLocalRing R] (ϖ : R)
    (hϖ : maximalIdeal R = Ideal.span {ϖ}) (p : Polynomial R) (hp : ∃ i, IsUnit (p.coeff i)) :
    ¬ (Polynomial.C ϖ ∣ p) := by
  rintro ⟨q, rfl⟩
  obtain ⟨i, hi⟩ := hp
  rw [Polynomial.coeff_C_mul] at hi
  exact not_isUnit_unif ϖ hϖ (isUnit_of_mul_isUnit_left hi)

theorem exists_isUnit_coeff {R : Type u} [CommRing R] [IsLocalRing R] (ϖ : R)
    (hϖ : maximalIdeal R = Ideal.span {ϖ}) (p : Polynomial R) (hp : ¬ (Polynomial.C ϖ ∣ p)) :
    ∃ i, IsUnit (p.coeff i) := by
  by_contra h
  push Not at h
  apply hp
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro i
  have : p.coeff i ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr (h i)
  rw [hϖ] at this
  exact Ideal.mem_span_singleton.mp this

end PenC4

namespace PenSwitch
open Polynomial AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

section Generic

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]

theorem isIntegral_adjoin_aeval_of_monic (f : A) (P : R[X]) (hP : P.Monic) (hdeg : 0 < P.natDegree) :
    IsIntegral (Algebra.adjoin R {aeval f P}) f := by
  classical
  nontriviality ↥(Algebra.adjoin R {aeval f P})
  let S : Subalgebra R A := Algebra.adjoin R {aeval f P}
  let c : ↥S := ⟨aeval f P, Algebra.subset_adjoin (Set.mem_singleton _)⟩
  let Q : (↥S)[X] := P.map (algebraMap R ↥S) - C c
  have hmapm : (P.map (algebraMap R ↥S)).Monic := hP.map _
  have hQm : Q.Monic := by
    apply Monic.sub_of_left hmapm
    calc (C c).degree ≤ 0 := degree_C_le
      _ < (P.map (algebraMap R ↥S)).degree := by
          rw [hP.degree_map, ← natDegree_pos_iff_degree_pos]
          exact hdeg
  refine ⟨Q, hQm, ?_⟩
  change aeval f Q = 0
  rw [map_sub, aeval_map_algebraMap, aeval_C]
  exact sub_self _

theorem isIntegral_of_adjoin_le {S₁ S₂ : Subalgebra R A} (h : S₁ ≤ S₂) {x : A}
    (hx : IsIntegral ↥S₁ x) : IsIntegral ↥S₂ x :=
  hx.map_of_comp_eq (Subalgebra.inclusion h).toRingHom (RingHom.id A) (by ext; rfl)

theorem isIntegral_of_le_of_forall_isIntegral {S₁ S₂ : Subalgebra R A} (h : S₁ ≤ S₂)
    (hint : ∀ y : A, y ∈ S₂ → IsIntegral ↥S₁ y) {x : A} (hx : IsIntegral ↥S₂ x) : IsIntegral ↥S₁ x := by
  letI alg : Algebra ↥S₁ ↥S₂ := (Subalgebra.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower ↥S₁ ↥S₂ A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsIntegral ↥S₁ ↥S₂ := by
    refine ⟨fun y => ?_⟩
    have hy : IsIntegral ↥S₁ (y : A) := hint y y.2
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥S₁ ↥S₂ A) Subtype.val_injective).1 hy
  exact isIntegral_trans x hx

end Generic

section Frame

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (f : F)

theorem chartAlg_aeval_eq (P : Polynomial R) (hP : P.Monic) (hd : 0 < P.natDegree) :
    chartAlg R F {Polynomial.aeval f P} = chartAlg R F {f} := by
  have hle : Algebra.adjoin R {Polynomial.aeval f P} ≤ Algebra.adjoin R {f} :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 (aeval_mem_adjoin_singleton R f))
  apply le_antisymm
  · intro x hx
    rw [mem_chartAlg_iff] at hx ⊢
    exact isIntegral_of_adjoin_le hle hx
  · intro x hx
    rw [mem_chartAlg_iff] at hx ⊢
    refine isIntegral_of_le_of_forall_isIntegral hle (fun y hy => ?_) hx

    have hf : IsIntegral ↥(Algebra.adjoin R {Polynomial.aeval f P}) f :=
      isIntegral_adjoin_aeval_of_monic f P hP hd
    have : Algebra.adjoin R {f} ≤ (integralClosure ↥(Algebra.adjoin R {Polynomial.aeval f P}) F).restrictScalars R := by
      refine Algebra.adjoin_le (Set.singleton_subset_iff.2 ?_)
      exact hf
    exact this hy

variable [IsDomain R]

theorem transcendental_aeval (htf : Transcendental R f) (P : Polynomial R) (hP : P.Monic)
    (hd : 0 < P.natDegree) : Transcendental R (Polynomial.aeval f P) :=
  htf.aeval P (Nat.pos_iff_ne_zero.1 hd) (by rw [hP.leadingCoeff]; exact one_mem _)

theorem C_dvd_iff_map_eq_zero (ϖ : R) (Q : Polynomial R) :
    C ϖ ∣ Q ↔ Q.map (Ideal.Quotient.mk (Ideal.span {ϖ})) = 0 := by
  rw [C_dvd_iff_dvd_coeff]
  constructor
  · intro h
    ext n
    rw [coeff_map, coeff_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact h n
  · intro h n
    have := congrArg (fun q => q.coeff n) h
    simp only [coeff_map, coeff_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
    exact this

theorem overGauss_aeval [IsDiscreteValuationRing R] (ϖ : R)
    (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (O : ValuationSubring F)
    (hO : ∀ Q : Polynomial R, ¬ (Polynomial.C ϖ ∣ Q) →
      Polynomial.aeval f Q ∈ O ∧ (Polynomial.aeval f Q)⁻¹ ∈ O)
    (P : Polynomial R) (hP : P.Monic) (hd : 0 < P.natDegree) :
    ∀ Q : Polynomial R, ¬ (Polynomial.C ϖ ∣ Q) →
      Polynomial.aeval (Polynomial.aeval f P) Q ∈ O ∧ (Polynomial.aeval (Polynomial.aeval f P) Q)⁻¹ ∈ O := by
  classical
  intro Q hQ
  rw [← aeval_comp]
  apply hO

  haveI hmax : (Ideal.span {ϖ} : Ideal R).IsMaximal := hϖ ▸ IsLocalRing.maximalIdeal.isMaximal R
  letI : Field (R ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field (Ideal.span {ϖ})
  rw [C_dvd_iff_map_eq_zero] at hQ ⊢
  rw [map_comp]
  intro h
  have hPm : (P.map (Ideal.Quotient.mk (Ideal.span {ϖ}))).Monic := hP.map _
  have hPd : 0 < (P.map (Ideal.Quotient.mk (Ideal.span {ϖ}))).natDegree := by
    rw [hP.natDegree_map]; exact hd
  rcases (comp_eq_zero_iff.1 h) with h0 | ⟨-, hC⟩
  · exact hQ h0
  · have := congrArg natDegree hC
    rw [natDegree_C] at this
    exact absurd this (Nat.pos_iff_ne_zero.1 hPd)

end Frame

section P5

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
  (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
  (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F] (f : F)

theorem isIntegral_polynomialToChartFin [Fact (f ≠ 0)] :
    (polynomialToChartFin R F f).toRingHom.IsIntegral := by
  classical
  intro x

  let B : Subalgebra R F := Algebra.adjoin R {f}
  let fB : ↥B := ⟨f, Algebra.self_mem_adjoin_singleton R f⟩
  let g : R[X] →+* ↥B := (aeval fB).toRingHom
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨q, hq⟩ : (y : F) ∈ (aeval (R := R) f).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval R f]; exact y.2
    refine ⟨q, Subtype.ext ?_⟩
    change ((aeval fB q : ↥B) : F) = y
    rw [aeval_subalgebra_coe]; exact hq
  have hx : IsIntegral ↥B (x : F) := (mem_chartAlg_iff R F).1 x.2
  obtain ⟨p, hpm, hpx⟩ := hx
  obtain ⟨P', hP'map, -, hP'm⟩ := lifts_and_natDegree_eq_and_monic ((mem_lifts p).2 (map_surjective g hg p)) hpm
  refine ⟨P', hP'm, ?_⟩
  apply Subtype.val_injective
  change ((eval₂ (polynomialToChartFin R F f).toRingHom x P' : ↥(chartAlgFin R F f)) : F) = ((0 : ↥(chartAlgFin R F f)) : F)
  rw [show ((eval₂ (polynomialToChartFin R F f).toRingHom x P' : ↥(chartAlgFin R F f)) : F) =
      eval₂ ((chartAlgFin R F f).val.toRingHom.comp (polynomialToChartFin R F f).toRingHom) (x : F) P' from
    hom_eval₂ P' (polynomialToChartFin R F f).toRingHom (chartAlgFin R F f).val.toRingHom x]
  have hcomp : (chartAlgFin R F f).val.toRingHom.comp (polynomialToChartFin R F f).toRingHom =
      B.val.toRingHom.comp g := by
    ext q
    · simp [g, fB, polynomialToChartFin]
    · simp [g, fB, polynomialToChartFin, jChartFin]
  rw [hcomp, ← eval₂_map, hP'map]
  change eval₂ (algebraMap ↥B F) (x : F) p = 0
  exact hpx

include hϖ in
omit [Algebra R K₀] [IsFractionRing R K₀] [IsScalarTower R K₀ F] in

theorem exists_monic_aeval_mem [Fact (f ≠ 0)] (htf : Transcendental R f)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    {ι : Type u} [Fintype ι] (𝔪 : ι → Ideal ↥(chartAlgFin R F f)) (h𝔪 : ∀ i, (𝔪 i).IsMaximal)
    (hϖ𝔪 : ∀ i, algebraMap R _ ϖ ∈ 𝔪 i) :
    ∃ P : Polynomial R, P.Monic ∧ 0 < P.natDegree ∧ ∀ i, Polynomial.aeval (jChartFin R F f) P ∈ 𝔪 i := by
  classical

  haveI hmax : (Ideal.span {ϖ} : Ideal R).IsMaximal := hϖ ▸ IsLocalRing.maximalIdeal.isMaximal R
  letI : Field (R ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field (Ideal.span {ϖ})
  let mk : R →+* R ⧸ Ideal.span {ϖ} := Ideal.Quotient.mk _
  let πk : R[X] →+* (R ⧸ Ideal.span {ϖ})[X] := mapRingHom mk
  have hπk : Function.Surjective πk := map_surjective mk Ideal.Quotient.mk_surjective
  have hkerπ : ∀ q : R[X], πk q = 0 → C ϖ ∣ q := fun q hq =>
    (C_dvd_iff_map_eq_zero R ϖ q).2 hq
  let φ : R[X] →+* ↥(chartAlgFin R F f) := (polynomialToChartFin R F f).toRingHom
  have hφ : ∀ q, φ q = Polynomial.aeval (jChartFin R F f) q := fun q => rfl
  have hφint : φ.IsIntegral := isIntegral_polynomialToChartFin R F f
  have hφC : φ (C ϖ) = algebraMap R _ ϖ := by rw [hφ, aeval_C]

  have one : ∀ i, ∃ P : Polynomial R, P.Monic ∧ 0 < P.natDegree ∧ Polynomial.aeval (jChartFin R F f) P ∈ 𝔪 i := by
    intro i
    haveI := h𝔪 i
    let 𝔫 : Ideal R[X] := (𝔪 i).comap φ
    haveI h𝔫 : 𝔫.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' φ hφint (𝔪 i)
    have hC𝔫 : C ϖ ∈ 𝔫 := by rw [Ideal.mem_comap, hφC]; exact hϖ𝔪 i

    let 𝔫' : Ideal (R ⧸ Ideal.span {ϖ})[X] := 𝔫.map πk
    have h𝔫'top : 𝔫' ≠ ⊤ := by
      intro htop
      have h1 : (1 : (R ⧸ Ideal.span {ϖ})[X]) ∈ 𝔫' := htop ▸ Submodule.mem_top
      obtain ⟨n, hn, hn1⟩ := (Ideal.mem_map_iff_of_surjective πk hπk).1 h1
      apply h𝔫.ne_top
      rw [Ideal.eq_top_iff_one]
      have hdiff : C ϖ ∣ (1 - n) := hkerπ _ (by rw [map_sub, hn1, map_one, sub_self])
      obtain ⟨r, hr⟩ := hdiff
      have : (1 : R[X]) = n + C ϖ * r := by rw [← hr]; ring
      rw [this]
      exact 𝔫.add_mem hn (𝔫.mul_mem_right _ hC𝔫)
    have h𝔫' : 𝔫'.IsMaximal := by
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective πk hπk h𝔫 with h | h
      · exact absurd h h𝔫'top
      · exact h

    have h𝔫'bot : 𝔫' ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔫' (Polynomial.not_isField _)
    obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal 𝔫')
    have hg0 : g ≠ 0 := by
      intro h0; apply h𝔫'bot; rw [hg, h0]; simp
    let p : (R ⧸ Ideal.span {ϖ})[X] := g * C (leadingCoeff g)⁻¹
    have hpm : p.Monic := monic_mul_leadingCoeff_inv hg0
    have hp𝔫' : p ∈ 𝔫' := by
      rw [hg]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self g)
    have hpdeg : 0 < p.natDegree := by
      by_contra hle
      push Not at hle
      have hp1 : p = 1 := by
        rw [Polynomial.eq_one_of_monic_natDegree_zero hpm (Nat.le_zero.1 hle)]
      apply h𝔫'top
      rw [Ideal.eq_top_iff_one, ← hp1]; exact hp𝔫'

    obtain ⟨P, hPmap, hPdeg, hPm⟩ :=
      lifts_and_natDegree_eq_and_monic ((mem_lifts p).2 (map_surjective mk Ideal.Quotient.mk_surjective p)) hpm
    refine ⟨P, hPm, hPdeg ▸ hpdeg, ?_⟩
    obtain ⟨n, hn, hnp⟩ := (Ideal.mem_map_iff_of_surjective πk hπk).1 hp𝔫'
    have hdiff : C ϖ ∣ (P - n) := hkerπ _ (by
      rw [map_sub, hnp]
      change P.map mk - p = 0
      rw [hPmap, sub_self])
    obtain ⟨r, hr⟩ := hdiff
    have hP𝔫 : P ∈ 𝔫 := by
      have : P = n + C ϖ * r := by rw [← hr]; ring
      rw [this]; exact 𝔫.add_mem hn (𝔫.mul_mem_right _ hC𝔫)
    rw [← hφ]
    exact (Ideal.mem_comap.1 hP𝔫)

  choose P hPm hPd hPi using one
  by_cases hι : Nonempty ι
  · obtain ⟨i₀⟩ := hι
    refine ⟨∏ i, P i, monic_prod_of_monic _ _ (fun i _ => hPm i), ?_, fun i => ?_⟩
    · rw [natDegree_prod_of_monic _ _ (fun i _ => hPm i)]
      exact Finset.sum_pos (fun i _ => hPd i) ⟨i₀, Finset.mem_univ _⟩
    · rw [map_prod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      exact Ideal.mul_mem_left _ _ (hPi i)
  · refine ⟨X, monic_X, by simp, fun i => (hι ⟨i⟩).elim⟩

end P5

section P3

variable (R : Type u) [CommRing R]
  (K₀ : Type u) [Field K₀] [Algebra R K₀]
  (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F] (f : F)

theorem finiteDimensional_and_isSeparable_adjoin_aeval [CharZero K₀]
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    (P : Polynomial R) (hP : P.Monic) (hd : 0 < P.natDegree) :
    FiniteDimensional ↥(IntermediateField.adjoin K₀ ({Polynomial.aeval f P} : Set F)) F ∧
      Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({Polynomial.aeval f P} : Set F)) F := by
  classical
  set g : F := Polynomial.aeval f P with hgdef
  let E₁ : IntermediateField K₀ F := IntermediateField.adjoin K₀ ({g} : Set F)
  let E₂ : IntermediateField K₀ F := IntermediateField.adjoin K₀ ({f} : Set F)

  have hgE₂ : g ∈ E₂ := by
    have h1 : g = Polynomial.aeval f (P.map (algebraMap R K₀)) := by
      rw [hgdef, Polynomial.aeval_map_algebraMap]
    rw [h1]
    exact IntermediateField.algebra_adjoin_le_adjoin K₀ _ (Polynomial.aeval_mem_adjoin_singleton K₀ f)
  have hle : E₁ ≤ E₂ := IntermediateField.adjoin_le_iff.2 (Set.singleton_subset_iff.2 hgE₂)

  haveI : IsScalarTower R ↥E₁ F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hfint : IsIntegral ↥E₁ f := by
    let c : ↥E₁ := ⟨g, IntermediateField.subset_adjoin K₀ _ (Set.mem_singleton g)⟩
    let Q : (↥E₁)[X] := P.map (algebraMap R ↥E₁) - C c
    have hmapm : (P.map (algebraMap R ↥E₁)).Monic := hP.map _
    have hQm : Q.Monic := by
      apply Monic.sub_of_left hmapm
      calc (C c).degree ≤ 0 := degree_C_le
        _ < (P.map (algebraMap R ↥E₁)).degree := by
            rw [hP.degree_map, ← natDegree_pos_iff_degree_pos]; exact hd
    refine ⟨Q, hQm, ?_⟩
    change Polynomial.aeval f Q = 0
    rw [map_sub, Polynomial.aeval_map_algebraMap, aeval_C, ← hgdef]
    exact sub_self _

  have hext : IntermediateField.extendScalars hle = IntermediateField.adjoin ↥E₁ ({f} : Set F) :=
    IntermediateField.extendScalars_adjoin hle
  haveI hfin₁ : FiniteDimensional ↥E₁ ↥(IntermediateField.extendScalars hle) := by
    rw [hext]; exact IntermediateField.adjoin.finiteDimensional hfint
  haveI hfin₂ : Module.Finite ↥(IntermediateField.extendScalars hle) F := hFD
  have hfin : FiniteDimensional ↥E₁ F := Module.Finite.trans ↥(IntermediateField.extendScalars hle) F
  refine ⟨hfin, ?_⟩
  haveI := hfin
  haveI : Algebra.IsAlgebraic ↥E₁ F := Algebra.IsAlgebraic.of_finite ↥E₁ F
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

end P3

end PenSwitch

open PenC4 in
theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (K₀ : Type u) [Field K₀] [CharZero K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (f : F) (htf : Transcendental R f)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    (V : Finset (ValuationSubring F)) (hV : V.Nonempty)
    (hVf : ∀ O ∈ V, (∀ a : R, algebraMap R F a ∈ O) ∧ algebraMap R F ϖ ∈ O.nonunits ∧
      ∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval f P ∈ O ∧ (Polynomial.aeval f P)⁻¹ ∈ O) :
    ∃ g : F, Transcendental R g ∧
      FiniteDimensional ↥(IntermediateField.adjoin K₀ ({g} : Set F)) F ∧
      Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({g} : Set F)) F ∧
      ∀ O : ValuationSubring F, (∀ a : R, algebraMap R F a ∈ O) → algebraMap R F ϖ ∈ O.nonunits →
        ((∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval g P ∈ O ∧ (Polynomial.aeval g P)⁻¹ ∈ O) ↔ O ∈ V) := by
  classical
  have hf0 : f ≠ 0 := fun h => htf (h ▸ isAlgebraic_zero)
  haveI : Fact (f ≠ 0) := ⟨hf0⟩
  have hinjT : Function.Injective (Polynomial.aeval (R := R) f) := transcendental_iff_injective.mp htf

  have hRF : Function.Injective (algebraMap R F) := by
    rw [IsScalarTower.algebraMap_eq R K₀ F]
    exact (algebraMap K₀ F).injective.comp (IsFractionRing.injective R K₀)
  have hRA : Function.Injective (algebraMap R ↥(chartAlgFin R F f)) := by
    intro a b hab
    apply hRF
    have := congrArg (fun x : ↥(chartAlgFin R F f) => (x : F)) hab
    simpa using this

  obtain ⟨hFT, -⟩ := AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf R K₀ F f htf hFD hsep
  haveI := hFT
  haveI : IsNoetherianRing ↥(chartAlgFin R F f) := Algebra.FiniteType.isNoetherianRing R _
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F := Algebra.IsAlgebraic.of_finite _ _
  have hfrac : IsFractionRing ↥(chartAlgFin R F f) F :=
    AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg R K₀ F {f}
  haveI := hfrac
  haveI : IsIntegrallyClosed ↥(chartAlgFin R F f) := by
    rw [isIntegrallyClosed_iff F]
    intro x hx

    let S : Subalgebra R F := Algebra.adjoin R ({f} : Set F)
    have hSA : S ≤ chartAlgFin R F f := adjoin_le_chartAlg R F {f}
    letI : Algebra ↥S ↥(chartAlgFin R F f) := (Subalgebra.inclusion hSA).toAlgebra
    haveI : IsScalarTower ↥S ↥(chartAlgFin R F f) F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : Algebra.IsIntegral ↥S ↥(chartAlgFin R F f) := ⟨fun y =>
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥S ↥(chartAlgFin R F f) F) Subtype.val_injective).mp y.2⟩
    have hxS : IsIntegral ↥S x := isIntegral_trans x hx
    exact ⟨⟨x, (mem_chartAlg_iff R F).mpr hxS⟩, rfl⟩

  have hϖnu : ¬ IsUnit ϖ := not_isUnit_unif ϖ hϖ

  have stepA : ∀ O ∈ V, ∃ 𝔮 : Ideal ↥(chartAlgFin R F f),
      𝔮 ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F f) ϖ}).minimalPrimes ∧
      (∀ y : F, y ∈ O ↔ ∃ b c : ↥(chartAlgFin R F f), c ∉ 𝔮 ∧ y * (c : F) = (b : F)) ∧
      ¬ 𝔮.IsMaximal := by
    intro O hO
    obtain ⟨hRO, hϖO, hgauss⟩ := hVf O hO
    have hX : ¬ (Polynomial.C ϖ ∣ (Polynomial.X : Polynomial R)) :=
      not_C_dvd ϖ hϖ _ ⟨1, by simp⟩
    have hfO : f ∈ O := by simpa using (hgauss _ hX).1
    have hgeoO : ∀ p : Polynomial R, (∃ i, IsUnit (p.coeff i)) →
        ∃ hO' : Polynomial.eval₂ (algebraMap R F) f p ∈ O, IsUnit (⟨_, hO'⟩ : ↥O) := by
      intro p hp
      obtain ⟨hmem, hinv⟩ := hgauss p (not_C_dvd ϖ hϖ p hp)
      have hp0 : p ≠ 0 := by
        rintro rfl
        obtain ⟨i, hi⟩ := hp
        simp at hi
      have hne : Polynomial.aeval f p ≠ 0 := fun h => hp0 (hinjT (by rw [h, map_zero]))
      rw [Polynomial.aeval_def] at hmem hinv hne
      exact ⟨hmem, IsUnit.of_mul_eq_one (⟨_, hinv⟩ : ↥O) (by ext; simp [mul_inv_cancel₀ hne])⟩
    obtain ⟨hf0', -, -, -, -, -, hrest⟩ :=
      ValuationSubring.inv_mem_and_chartAlg_le_and_over_gauss_and_isDiscreteValuationRing_of_forall_isUnit_polynomialEval2
        R ϖ hϖ K₀ F O hRO hϖO f hfO hgeoO
    obtain ⟨-, h𝔭ex⟩ := hrest hFD hsep
    obtain ⟨𝔭, h𝔭all⟩ := h𝔭ex

    exact ⟨𝔭, h𝔭all.1, h𝔭all.2.2.2, h𝔭all.2.1⟩
  choose 𝔮fun h𝔮fun using stepA
  let 𝔮 : ↥V → Ideal ↥(chartAlgFin R F f) := fun i => 𝔮fun i.1 i.2
  have h𝔮min : ∀ i, 𝔮 i ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F f) ϖ}).minimalPrimes :=
    fun i => (h𝔮fun i.1 i.2).1
  have h𝔮loc : ∀ i : ↥V, ∀ y : F, y ∈ (↑i : ValuationSubring F) ↔
      ∃ b c : ↥(chartAlgFin R F f), c ∉ 𝔮 i ∧ y * (c : F) = (b : F) := fun i => (h𝔮fun i.1 i.2).2.1
  have h𝔮nm : ∀ i, ¬ (𝔮 i).IsMaximal := fun i => (h𝔮fun i.1 i.2).2.2
  have h𝔮prime : ∀ i, (𝔮 i).IsPrime := fun i => (h𝔮min i).1.1
  have hϖ𝔮 : ∀ i, algebraMap R ↥(chartAlgFin R F f) ϖ ∈ 𝔮 i := fun i => (h𝔮min i).1.2 (Ideal.mem_span_singleton_self _)

  have h𝔮inj : ∀ i j, 𝔮 i = 𝔮 j → i = j := by
    intro i j hij
    apply Subtype.ext
    ext y
    rw [h𝔮loc i y, h𝔮loc j y, hij]

  haveI : (maximalIdeal R).IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
  have hmapI : Ideal.map (algebraMap R ↥(chartAlgFin R F f)) (maximalIdeal R) ≤
      Ideal.span {algebraMap R ↥(chartAlgFin R F f) ϖ} := by
    rw [hϖ, Ideal.map_span, Set.image_singleton]
  have hdim : ∀ i, ∀ P : Ideal ↥(chartAlgFin R F f), P.IsPrime → 𝔮 i < P → P.IsMaximal := by
    intro i P hP hlt
    haveI := hP
    rcases AlgebraicCurve.TwoChartIntegralModel.mem_minimalPrimes_or_isMaximal_of_mem_chartAlgFin R ϖ hϖ K₀ F f htf
        hFD hsep P (hlt.le (hϖ𝔮 i)) with hmin | hmax
    · exact absurd (hmin.2 ⟨h𝔮prime i, (h𝔮min i).1.2⟩ hlt.le) (not_le_of_gt hlt)
    · exact hmax
  have stepB : ∀ i : ↥V, ∃ 𝔪 : Ideal ↥(chartAlgFin R F f), 𝔪.IsMaximal ∧ 𝔮 i ≤ 𝔪 ∧
      ∀ 𝔮' ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F f) ϖ}).minimalPrimes, 𝔮' ≤ 𝔪 → 𝔮' = 𝔮 i :=
    fun i => Ideal.exists_isMaximal_forall_mem_minimalPrimes_le_imp_eq_of_finiteType (maximalIdeal R)
      (Ideal.span {algebraMap R ↥(chartAlgFin R F f) ϖ}) hmapI (𝔮 i) (h𝔮min i) (h𝔮nm i) (hdim i)
  choose 𝔪 h𝔪 using stepB
  have h𝔪max : ∀ i, (𝔪 i).IsMaximal := fun i => (h𝔪 i).1
  have h𝔮𝔪 : ∀ i, 𝔮 i ≤ 𝔪 i := fun i => (h𝔪 i).2.1
  have honly : ∀ i, ∀ 𝔮' ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F f) ϖ}).minimalPrimes, 𝔮' ≤ 𝔪 i → 𝔮' = 𝔮 i :=
    fun i => (h𝔪 i).2.2
  have hϖ𝔪 : ∀ i, algebraMap R ↥(chartAlgFin R F f) ϖ ∈ 𝔪 i := fun i => h𝔮𝔪 i (hϖ𝔮 i)
  have hinj : Function.Injective 𝔪 := by
    intro i j hij
    exact h𝔮inj i j (honly j (𝔮 i) (h𝔮min i) (hij ▸ h𝔮𝔪 i))

  obtain ⟨P, hPmonic, hPdeg, hP𝔪⟩ :=
    PenSwitch.exists_monic_aeval_mem R ϖ hϖ K₀ F f htf hFD hsep 𝔪 h𝔪max hϖ𝔪

  have hΦ : (fun S : Subalgebra R F => ∃ hPS : Polynomial.aeval f P ∈ S,
      ∀ i : ↥V, ∃ 𝔮' 𝔪' : Ideal ↥S,
        𝔮' ∈ (Ideal.span {algebraMap R ↥S ϖ}).minimalPrimes ∧ ¬ 𝔮'.IsMaximal ∧
        (∀ y : F, y ∈ (↑i : ValuationSubring F) ↔ ∃ b c : ↥S, c ∉ 𝔮' ∧ y * (c : F) = (b : F)) ∧
        𝔪'.IsMaximal ∧ 𝔮' ≤ 𝔪' ∧ (⟨Polynomial.aeval f P, hPS⟩ : ↥S) ∈ 𝔪' ∧
        (∀ 𝔮'' ∈ (Ideal.span {algebraMap R ↥S ϖ}).minimalPrimes, 𝔮'' ≤ 𝔪' → 𝔮'' = 𝔮'))
      (chartAlgFin R F f) := by
    have hcoe : ((Polynomial.aeval (jChartFin R F f) P : ↥(chartAlgFin R F f)) : F) = Polynomial.aeval f P := by
      have := Polynomial.aeval_algHom_apply (chartAlgFin R F f).val (jChartFin R F f) P
      simpa using this.symm
    have hPS : Polynomial.aeval f P ∈ chartAlgFin R F f := hcoe ▸ (Polynomial.aeval (jChartFin R F f) P).2
    refine ⟨hPS, fun i => ⟨𝔮 i, 𝔪 i, h𝔮min i, h𝔮nm i, h𝔮loc i, h𝔪max i, h𝔮𝔪 i, ?_, honly i⟩⟩
    have heq : (⟨Polynomial.aeval f P, hPS⟩ : ↥(chartAlgFin R F f)) = Polynomial.aeval (jChartFin R F f) P :=
      Subtype.ext hcoe.symm
    rw [heq]; exact hP𝔪 i
  set f₁ : F := Polynomial.aeval f P with hf₁
  have hf₁0 : f₁ ≠ 0 := by
    intro h
    have hP0 : P ≠ 0 := hPmonic.ne_zero
    exact hP0 (hinjT (by rw [map_zero]; exact h))
  haveI hF1 : Fact (f₁ ≠ 0) := ⟨hf₁0⟩
  have e : chartAlgFin R F f₁ = chartAlgFin R F f := PenSwitch.chartAlg_aeval_eq R F f P hPmonic hPdeg
  have hΦ₁ := (e.symm ▸ hΦ :)
  obtain ⟨hPS₁, hΦ₁'⟩ := hΦ₁
  choose 𝔮₁ 𝔪₁ hΦ₁'' using hΦ₁'

  have htf₁ : Transcendental R f₁ := PenSwitch.transcendental_aeval R F f htf P hPmonic hPdeg
  obtain ⟨hFD₁, hsep₁⟩ := PenSwitch.finiteDimensional_and_isSeparable_adjoin_aeval R K₀ F f hFD P hPmonic hPdeg
  have hVf₁ : ∀ O ∈ V, ∀ Q : Polynomial R, ¬ (Polynomial.C ϖ ∣ Q) →
      Polynomial.aeval f₁ Q ∈ O ∧ (Polynomial.aeval f₁ Q)⁻¹ ∈ O :=
    fun O hO => PenSwitch.overGauss_aeval R F f ϖ hϖ O (hVf O hO).2.2 P hPmonic hPdeg

  have h𝔮₁min : ∀ i, 𝔮₁ i ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F f₁) ϖ}).minimalPrimes := fun i => (hΦ₁'' i).1
  have h𝔮₁loc : ∀ i : ↥V, ∀ y : F, y ∈ (↑i : ValuationSubring F) ↔
      ∃ b c : ↥(chartAlgFin R F f₁), c ∉ 𝔮₁ i ∧ y * (c : F) = (b : F) := fun i => (hΦ₁'' i).2.2.1
  have h𝔪₁max : ∀ i, (𝔪₁ i).IsMaximal := fun i => (hΦ₁'' i).2.2.2.1
  have h𝔮𝔪₁ : ∀ i, 𝔮₁ i ≤ 𝔪₁ i := fun i => (hΦ₁'' i).2.2.2.2.1
  have hf𝔪₁ : ∀ i, jChartFin R F f₁ ∈ 𝔪₁ i := fun i => by
    have := (hΦ₁'' i).2.2.2.2.2.1
    convert this using 1 <;> try first | with_reducible_and_instances rfl | rfl
  have honly₁ : ∀ i, ∀ 𝔮'' ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F f₁) ϖ}).minimalPrimes, 𝔮'' ≤ 𝔪₁ i → 𝔮'' = 𝔮₁ i :=
    fun i => (hΦ₁'' i).2.2.2.2.2.2
  have hϖ𝔪₁ : ∀ i, algebraMap R ↥(chartAlgFin R F f₁) ϖ ∈ 𝔪₁ i :=
    fun i => h𝔮𝔪₁ i ((h𝔮₁min i).1.2 (Ideal.mem_span_singleton_self _))
  have hinj₁ : Function.Injective 𝔪₁ := by
    intro i j hij
    apply Subtype.ext; ext y
    rw [h𝔮₁loc i y, h𝔮₁loc j y, honly₁ j (𝔮₁ i) (h𝔮₁min i) (hij ▸ h𝔮𝔪₁ i)]

  have hf𝔮₁ : ∀ i, jChartFin R F f₁ ∉ 𝔮₁ i := by
    intro i hmem
    have hX : ¬ (Polynomial.C ϖ ∣ (Polynomial.X : Polynomial R)) := not_C_dvd ϖ hϖ _ ⟨1, by simp⟩
    have hinv : f₁⁻¹ ∈ (↑i : ValuationSubring F) := by simpa using (hVf₁ i.1 i.2 _ hX).2
    obtain ⟨b, c, hc, hbc⟩ := (h𝔮₁loc i f₁⁻¹).mp hinv
    apply hc
    have hcb : c = jChartFin R F f₁ * b := by
      apply Subtype.ext
      simp only [Subalgebra.coe_mul, coe_jChartFin]
      rw [← hbc, ← mul_assoc, mul_inv_cancel₀ hf₁0, one_mul]
    rw [hcb]
    exact Ideal.mul_mem_right _ _ hmem

  obtain ⟨hFT₁, -⟩ := AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf R K₀ F f₁ htf₁ hFD₁ hsep₁
  haveI := hFT₁
  haveI : IsNoetherianRing ↥(chartAlgFin R F f₁) := Algebra.FiniteType.isNoetherianRing R _
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin K₀ ({f₁} : Set F)) F := Algebra.IsAlgebraic.of_finite _ _
  haveI hfrac₁ : IsFractionRing ↥(chartAlgFin R F f₁) F :=
    AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg R K₀ F {f₁}
  haveI : IsIntegrallyClosed ↥(chartAlgFin R F f₁) := by
    rw [isIntegrallyClosed_iff F]
    intro x hx
    let S : Subalgebra R F := Algebra.adjoin R ({f₁} : Set F)
    have hSA : S ≤ chartAlgFin R F f₁ := adjoin_le_chartAlg R F {f₁}
    letI : Algebra ↥S ↥(chartAlgFin R F f₁) := (Subalgebra.inclusion hSA).toAlgebra
    haveI : IsScalarTower ↥S ↥(chartAlgFin R F f₁) F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : Algebra.IsIntegral ↥S ↥(chartAlgFin R F f₁) := ⟨fun y =>
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥S ↥(chartAlgFin R F f₁) F) Subtype.val_injective).mp y.2⟩
    have hxS : IsIntegral ↥S x := isIntegral_trans x hx
    exact ⟨⟨x, (mem_chartAlg_iff R F).mpr hxS⟩, rfl⟩
  have hRA₁ : Function.Injective (algebraMap R ↥(chartAlgFin R F f₁)) := by
    intro a b hab
    apply hRF
    have := congrArg (fun x : ↥(chartAlgFin R F f₁) => (x : F)) hab
    simpa using this
  have hisolAll : ∀ i (Q : Ideal ↥(chartAlgFin R F f₁)), Q.IsPrime → jChartFin R F f₁ ∈ Q →
      algebraMap R ↥(chartAlgFin R F f₁) ϖ ∈ Q → Q ≤ 𝔪₁ i → Q = 𝔪₁ i := by
    intro i Q hQ hfQ hϖQ hle
    haveI := hQ
    rcases AlgebraicCurve.TwoChartIntegralModel.mem_minimalPrimes_or_isMaximal_of_mem_chartAlgFin R ϖ hϖ K₀ F f₁ htf₁
        hFD₁ hsep₁ Q hϖQ with hmin | hmax
    · have hQq : Q = 𝔮₁ i := honly₁ i Q hmin hle
      exact absurd (hQq ▸ hfQ : jChartFin R F f₁ ∈ 𝔮₁ i) (hf𝔮₁ i)
    · exact hmax.eq_of_le (h𝔪₁max i).ne_top hle
  have stepC : ∀ i : ↥V, ∃ I : Ideal ↥(chartAlgFin R F f₁),
      (∀ a : ↥(chartAlgFin R F f₁), a ∈ I ↔ ∃ s : ↥(chartAlgFin R F f₁), s ∉ 𝔪₁ i ∧ s * a ∈ Ideal.span {jChartFin R F f₁}) ∧
      jChartFin R F f₁ ∈ I ∧
      Module.Finite R (↥(chartAlgFin R F f₁) ⧸ I) ∧
      (∀ y : ↥(chartAlgFin R F f₁) ⧸ I, algebraMap R (↥(chartAlgFin R F f₁) ⧸ I) ϖ * y = 0 → y = 0) ∧
      (∀ Q : Ideal ↥(chartAlgFin R F f₁), Q.IsPrime → I ≤ Q → Q ≤ 𝔪₁ i) := by
    intro i
    haveI := h𝔪₁max i
    have hreg : ∀ a : ↥(chartAlgFin R F f₁), jChartFin R F f₁ * a ∈ Ideal.span {algebraMap R ↥(chartAlgFin R F f₁) ϖ} →
        ∃ s : ↥(chartAlgFin R F f₁), s ∉ 𝔪₁ i ∧ s * a ∈ Ideal.span {algebraMap R ↥(chartAlgFin R F f₁) ϖ} :=
      fun a ha => IsIntegrallyClosed.exists_not_mem_and_mul_mem_span_singleton_of_forall_mem_minimalPrimes_not_mem
        (algebraMap R ↥(chartAlgFin R F f₁) ϖ) (𝔪₁ i) (jChartFin R F f₁)
        (fun 𝔮' h𝔮' hle => by rw [honly₁ i 𝔮' h𝔮' hle]; exact hf𝔮₁ i) a ha
    obtain ⟨I, hI, htI, -, hfin, htor, hle⟩ :=
      HenselianLocalRing.exists_ideal_moduleFinite_quotient_of_forall_isPrime_imp_eq_of_isDiscreteValuationRing
        ϖ hϖ hRA₁ (𝔪₁ i) (hϖ𝔪₁ i) (jChartFin R F f₁) (hf𝔪₁ i) (hisolAll i) hreg
    exact ⟨I, hI, htI, hfin, htor, hle⟩
  choose I hIall using stepC

  obtain ⟨n, hn, g, h1, h2, h3⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_forall_mem_localization_chartAlg_and_mul_pow_jChartFin_isUnit_of_branchData
      R ϖ hϖ K₀ F f₁ htf₁ hFD₁ hsep₁ 𝔪₁ h𝔪₁max hinj₁ hϖ𝔪₁ hf𝔪₁ I (fun i => (hIall i).1) (fun i => (hIall i).2.2.1)
      (fun i => (hIall i).2.2.2.1) (fun i => (hIall i).2.2.2.2) hisolAll
  have h3' : ∀ i, ∃ b c : ↥(chartAlgFin R F f₁), b ∉ 𝔪₁ i ∧ c ∉ 𝔪₁ i ∧
      g * ((fun _ : ↥V => jChartFin R F f₁) i : F) ^ n * (c : F) = (b : F) := by
    intro i; simpa using h3 i
  obtain ⟨htg, hiff⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.forall_over_gauss_iff_exists_forall_mem_iff_of_mul_pow_isUnit_of_forall_mem_localization
      R ϖ hϖ K₀ F f₁ htf₁ hFD₁ hsep₁ 𝔮₁ h𝔮₁min 𝔪₁ h𝔪₁max h𝔮𝔪₁ honly₁ (fun _ => jChartFin R F f₁) hf𝔪₁ hf𝔮₁ I
      (fun i => (hIall i).2.1) (fun i => (hIall i).2.2.2.2) n hn g h1 h2 h3'
  obtain ⟨O₁, hO₁⟩ := hV
  have htg' : Transcendental R g := htg ⟨⟨O₁, hO₁⟩⟩

  have htfK : Transcendental K₀ f₁ := fun h => htf₁ ((IsFractionRing.isAlgebraic_iff R K₀ F).mpr h)
  have htgK : Transcendental K₀ g := fun h => htg' ((IsFractionRing.isAlgebraic_iff R K₀ F).mpr h)
  haveI : IsCurveOver K₀ F := AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable K₀ F f₁ htfK hFD₁ hsep₁
  haveI : Algebra.EssFiniteType K₀ F := AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional htfK hFD₁
  have hFDg : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({g} : Set F)) F :=
    AlgebraicCurve.IsCurveOver.finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType htgK
  haveI := hFDg
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K₀ F).injective
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin K₀ ({g} : Set F)) F := Algebra.IsAlgebraic.of_finite _ _
  have hsepg : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({g} : Set F)) F := inferInstance
  refine ⟨g, htg', hFDg, hsepg, ?_⟩
  intro O hRO hϖO
  refine (hiff O hRO hϖO).trans ⟨?_, ?_⟩
  · rintro ⟨i, hi⟩
    have : O = (i : ValuationSubring F) := by
      ext y
      exact (hi y).trans ((h𝔮₁loc i y).symm)
    rw [this]; exact i.2
  · intro hO
    exact ⟨⟨O, hO⟩, fun y => h𝔮₁loc ⟨O, hO⟩ y⟩

end S_ValuationSubring_exists_transcendental_forall_over_gauss_iff_mem_of_henselianLocalRing
end P2MW
export P2MW.S_ValuationSubring_exists_transcendental_forall_over_gauss_iff_mem_of_henselianLocalRing (solution)
