-- Prove2me | solution 1 for WeierstrassCurve.exists_mem_rationalHomSet_ker_eq_forall_exists_eq_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/ad78b976-dbf4-550d-91cf-147bc3609cc0

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import Theorems.Thm_WeierstrassCurve_veluPointHom_mem_rationalHomSet_and_exists_mem_rationalHomSet_comp_eq
import Theorems.Thm_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_veluPointHom_surjective_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq
import Theorems.Thm_WeierstrassCurve_exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul
import Theorems.Thm_WeierstrassCurve_veluPointMap2_surjective_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_veluQuotient2_Delta_ne_zero
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_ker_eq_forall_exists_eq_comp
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.pointAddEquivOfEq_refl"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_ker_eq_forall_exists_eq_comp.WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY a₃ a₁ map toAffine Affine.Point Δ baseChange rationalHomSet id_mem_rationalHomSet veluPointMap2 veluPointMap2_some_of_eq veluPointMap2_some_of_ne veluQuotient2 veluGy veluQuotient veluPointHom_mem_rationalHomSet_and_exists_mem_rationalHomSet_comp_eq oddOrderSummingSet exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed veluPointHom_surjective_of_isAlgClosed veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul veluPointMap2_surjective_of_isAlgClosed veluQuotient2_Delta_ne_zero comp_mem_rationalHomSet"
p2m_open "WeierstrassCurve"

namespace SeparableQuotientInduction

variable {κ : Type*} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

def Goal (E : WeierstrassCurve κ) (H : AddSubgroup E.toAffine.Point) : Prop :=
  ∃ (W : WeierstrassCurve κ) (_ : W.IsElliptic) (χ : E.toAffine.Point →+ W.toAffine.Point),
    χ ∈ rationalHomSet κ E W ∧ Function.Surjective χ ∧ χ.ker = H ∧
    ∀ (V : WeierstrassCurve κ) [V.IsElliptic] (α : E.toAffine.Point →+ V.toAffine.Point),
      α ∈ rationalHomSet κ E V → H ≤ α.ker → ∃ β ∈ rationalHomSet κ W V, α = β.comp χ

theorem goal_bot (E : WeierstrassCurve κ) [hE : E.IsElliptic] : Goal E ⊥ := by
  refine ⟨E, hE, AddMonoidHom.id _, id_mem_rationalHomSet κ E, Function.surjective_id, ?_, ?_⟩
  · ext P; simp
  · intro V _ α hα _
    exact ⟨α, hα, by ext P; rfl⟩

theorem goal_of_step (E E' : WeierstrassCurve κ) [E.IsElliptic] [E'.IsElliptic]
    (H : AddSubgroup E.toAffine.Point)
    (φ : E.toAffine.Point →+ E'.toAffine.Point) (hφ : φ ∈ rationalHomSet κ E E')
    (hφs : Function.Surjective φ) (hker : φ.ker ≤ H)
    (huniv : ∀ (V : WeierstrassCurve κ) [V.IsElliptic] (α : E.toAffine.Point →+ V.toAffine.Point),
      α ∈ rationalHomSet κ E V → φ.ker ≤ α.ker → ∃ β ∈ rationalHomSet κ E' V, α = β.comp φ)
    (hgoal : Goal E' (H.map φ)) : Goal E H := by
  obtain ⟨W, hW, χ', hχ', hχ's, hχ'ker, hχ'univ⟩ := hgoal
  refine ⟨W, hW, χ'.comp φ, comp_mem_rationalHomSet κ E E' W hφ hχ', hχ's.comp hφs, ?_, ?_⟩
  · ext P
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply]
    constructor
    · intro hP
      have hP' : φ P ∈ χ'.ker := hP
      rw [hχ'ker, AddSubgroup.mem_map] at hP'
      obtain ⟨h, hh, hhP⟩ := hP'
      have hdiff : P - h ∈ φ.ker := by
        rw [AddMonoidHom.mem_ker, map_sub, hhP, sub_self]
      have := hker hdiff
      simpa using H.add_mem this hh
    · intro hP
      have : φ P ∈ χ'.ker := by
        rw [hχ'ker]; exact AddSubgroup.mem_map_of_mem φ hP
      exact this
  · intro V _ α hα hHα
    obtain ⟨β, hβ, hαβ⟩ := huniv V α hα (hker.trans hHα)
    have hβker : H.map φ ≤ β.ker := by
      rintro _ ⟨h, hh, rfl⟩
      have : α h = 0 := hHα hh
      rw [hαβ] at this
      exact this
    obtain ⟨γ, hγ, hβγ⟩ := hχ'univ V β hβ hβker
    refine ⟨γ, hγ, ?_⟩
    rw [hαβ, hβγ]
    rfl

theorem exists_step_odd (E : WeierstrassCurve κ) [E.IsElliptic] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓκ : (ℓ : κ) ≠ 0) (Q : E.toAffine.Point) (hQ : addOrderOf Q = ℓ) :
    ∃ (E' : WeierstrassCurve κ) (_ : E'.IsElliptic) (φ : E.toAffine.Point →+ E'.toAffine.Point),
      φ ∈ rationalHomSet κ E E' ∧ Function.Surjective φ ∧ φ.ker = AddSubgroup.zmultiples Q ∧
      ∀ (V : WeierstrassCurve κ) [V.IsElliptic] (α : E.toAffine.Point →+ V.toAffine.Point),
        α ∈ rationalHomSet κ E V → φ.ker ≤ α.ker → ∃ β ∈ rationalHomSet κ E' V, α = β.comp φ := by
  have hodd : Odd ℓ := hℓ.odd_of_ne_two hℓ2
  have hQ' : addOrderOf Q = 2 * (ℓ / 2) + 1 := by rw [Nat.two_mul_div_two_add_one_of_odd hodd]; exact hQ
  obtain ⟨φ, hφker, hφfor⟩ :=
    exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed E hℓ hℓ2 hℓκ Q hQ
  have hΔ := veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq E (ℓ / 2) Q hQ'
  haveI hE' : (E.veluQuotient (E.oddOrderSummingSet Q (ℓ / 2))).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  obtain ⟨hφrat, hφuniv⟩ :=
    veluPointHom_mem_rationalHomSet_and_exists_mem_rationalHomSet_comp_eq E (ℓ / 2) Q hQ' φ hφker hφfor
  have hφs : Function.Surjective φ := veluPointHom_surjective_of_isAlgClosed E hℓ hℓ2 hℓκ Q hQ φ hφfor
  refine ⟨_, hE', φ, hφrat, hφs, hφker, ?_⟩
  intro V _ α hα hker
  have hαQ : α Q = 0 := by
    have : Q ∈ φ.ker := by rw [hφker]; exact AddSubgroup.mem_zmultiples Q
    exact hker this
  exact hφuniv V α hα hαQ

theorem eq_or_eq_negY_of_equation (E : WeierstrassCurve κ) {x₀ y₀ y : κ}
    (h₀ : E.toAffine.Equation x₀ y₀) (h : E.toAffine.Equation x₀ y) :
    y = y₀ ∨ y = E.toAffine.negY x₀ y₀ := by
  rw [equation_iff] at h₀ h
  have hprod : (y - y₀) * (y - E.toAffine.negY x₀ y₀) = 0 := by
    rw [WeierstrassCurve.Affine.negY]
    linear_combination h - h₀
  rcases mul_eq_zero.mp hprod with h1 | h1
  · exact Or.inl (sub_eq_zero.mp h1)
  · exact Or.inr (sub_eq_zero.mp h1)

theorem exists_step_two (E : WeierstrassCurve κ) [hE : E.IsElliptic] (h2 : (2 : κ) ≠ 0)
    (Q : E.toAffine.Point) (hQ : addOrderOf Q = 2) :
    ∃ (E' : WeierstrassCurve κ) (_ : E'.IsElliptic) (φ : E.toAffine.Point →+ E'.toAffine.Point),
      φ ∈ rationalHomSet κ E E' ∧ Function.Surjective φ ∧ φ.ker = AddSubgroup.zmultiples Q ∧
      ∀ (V : WeierstrassCurve κ) [V.IsElliptic] (α : E.toAffine.Point →+ V.toAffine.Point),
        α ∈ rationalHomSet κ E V → φ.ker ≤ α.ker → ∃ β ∈ rationalHomSet κ E' V, α = β.comp φ := by

  have hQ0 : Q ≠ 0 := by
    intro h; rw [h, addOrderOf_zero] at hQ; exact absurd hQ (by norm_num)
  have h2Q : (2 : ℕ) • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  rcases Q with _ | ⟨x₀, y₀, hns⟩
  · exact absurd rfl hQ0
  have heq : E.toAffine.Equation x₀ y₀ := hns.1
  have hneg : -(Point.some x₀ y₀ hns) = Point.some x₀ y₀ hns := by
    rw [neg_eq_iff_add_eq_zero, ← two_nsmul]; exact h2Q
  have hy₀ : E.toAffine.negY x₀ y₀ = y₀ := by
    rw [neg_some] at hneg
    exact ((some.injEq _ _ _ _ _ _).mp hneg).2
  have hgy : E.veluGy x₀ y₀ = 0 := by
    have : E.toAffine.negY x₀ y₀ = -y₀ - E.a₁ * x₀ - E.a₃ := rfl
    rw [this] at hy₀
    rw [WeierstrassCurve.veluGy]
    linear_combination hy₀
  have hΔE : E.Δ ≠ 0 := E.isUnit_Δ.ne_zero
  have hΔ : (E.veluQuotient2 x₀ y₀).Δ ≠ 0 := veluQuotient2_Delta_ne_zero hΔE heq hgy
  haveI hE' : (E.veluQuotient2 x₀ y₀).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  obtain ⟨π, hπcoe, hπrat, -, hπuniv⟩ :=
    exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul h2 E heq hgy hΔ
  have hπs : Function.Surjective π := by
    rw [hπcoe]; exact veluPointMap2_surjective_of_isAlgClosed E h2 heq hgy hΔ

  have hker : π.ker = AddSubgroup.zmultiples (Point.some x₀ y₀ hns) := by
    apply le_antisymm
    · intro P hP
      rw [AddMonoidHom.mem_ker] at hP
      rcases P with _ | ⟨x, y, hxy⟩
      · exact zero_mem _
      · by_cases hx : x = x₀
        · subst hx
          have hy : y = y₀ := by
            rcases eq_or_eq_negY_of_equation E heq hxy.1 with h | h
            · exact h
            · rw [h, hy₀]
          subst hy
          exact AddSubgroup.mem_zmultiples _
        · exfalso
          have h1 : π (Point.some x y hxy) = veluPointMap2 h2 heq hgy hΔ (Point.some x y hxy) := by
            rw [hπcoe]
          rw [veluPointMap2_some_of_ne h2 heq hgy hΔ hxy hx] at h1
          rw [h1] at hP
          exact absurd hP (by rintro ⟨⟩)
    · rw [AddSubgroup.zmultiples_le, AddMonoidHom.mem_ker]
      have h1 : π (Point.some x₀ y₀ hns) = veluPointMap2 h2 heq hgy hΔ (Point.some x₀ y₀ hns) := by
        rw [hπcoe]
      rw [h1, veluPointMap2_some_of_eq h2 heq hgy hΔ hns rfl]
      rfl
  refine ⟨_, hE', π, hπrat, hπs, hker, ?_⟩
  intro V hV α hα hle
  exact hπuniv V hV α hα (fun T hT => hle hT)

theorem card_eq_card_ker_mul_card_map {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (H : AddSubgroup A) (φ : A →+ B) :
    Nat.card H = Nat.card ((φ.comp H.subtype).ker) * Nat.card (H.map φ) := by
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (φ.comp H.subtype).ker
  have h2 : Nat.card (H ⧸ (φ.comp H.subtype).ker) = Nat.card (H.map φ) := by
    have e := QuotientAddGroup.quotientKerEquivRange (φ.comp H.subtype)
    rw [Nat.card_congr e.toEquiv, AddMonoidHom.range_comp, AddSubgroup.range_subtype]
  rw [h1, h2, mul_comm]

theorem card_ker_comp_subtype_of_ker_le {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (H : AddSubgroup A) (φ : A →+ B) (hle : φ.ker ≤ H) :
    Nat.card ((φ.comp H.subtype).ker) = Nat.card φ.ker := by
  have : (φ.comp H.subtype).ker = φ.ker.addSubgroupOf H := by
    ext x; simp [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker]
  rw [this]
  exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hle).toEquiv

theorem goal_of_card_eq (m : ℕ) :
    ∀ (E : WeierstrassCurve κ) (_ : E.IsElliptic) (H : AddSubgroup E.toAffine.Point),
      Nat.card H = m → (m : κ) ≠ 0 → Goal E H := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro E hE H hcard hm
  by_cases hbot : H = ⊥
  · subst hbot; exact goal_bot E
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
  haveI : Finite H := Nat.finite_of_card_ne_zero (hcard ▸ hm0)
  have hm1 : m ≠ 1 := by
    intro h; rw [h] at hcard; exact hbot (AddSubgroup.eq_bot_of_card_eq H hcard)
  obtain ⟨ℓ, hℓ, hℓm⟩ := Nat.exists_prime_and_dvd hm1
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fintype H := Fintype.ofFinite H
  have hℓH : ℓ ∣ Fintype.card H := by rw [Fintype.card_eq_nat_card, hcard]; exact hℓm
  obtain ⟨Q', hQ'⟩ := exists_prime_addOrderOf_dvd_card ℓ hℓH
  set Q : E.toAffine.Point := (Q' : E.toAffine.Point) with hQdef
  have hQord : addOrderOf Q = ℓ := by rw [hQdef, AddSubgroup.addOrderOf_coe, hQ']
  have hQH : Q ∈ H := Q'.2
  have hℓκ : (ℓ : κ) ≠ 0 := by
    obtain ⟨k, rfl⟩ := hℓm
    intro h; apply hm; push_cast; rw [h, zero_mul]

  obtain ⟨E', hE', φ, hφ, hφs, hφker, hφuniv⟩ :
      ∃ (E' : WeierstrassCurve κ) (_ : E'.IsElliptic) (φ : E.toAffine.Point →+ E'.toAffine.Point),
        φ ∈ rationalHomSet κ E E' ∧ Function.Surjective φ ∧ φ.ker = AddSubgroup.zmultiples Q ∧
        ∀ (V : WeierstrassCurve κ) [V.IsElliptic] (α : E.toAffine.Point →+ V.toAffine.Point),
          α ∈ rationalHomSet κ E V → φ.ker ≤ α.ker → ∃ β ∈ rationalHomSet κ E' V, α = β.comp φ := by
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      exact exists_step_two E hℓκ Q hQord
    · exact exists_step_odd E hℓ hℓ2 hℓκ Q hQord
  haveI := hE'
  have hkerH : φ.ker ≤ H := by
    rw [hφker, AddSubgroup.zmultiples_le]; exact hQH

  have hcardker : Nat.card φ.ker = ℓ := by
    rw [hφker, Nat.card_zmultiples, hQord]
  have hmul : m = ℓ * Nat.card (H.map φ) := by
    rw [← hcard, card_eq_card_ker_mul_card_map H φ, card_ker_comp_subtype_of_ker_le H φ hkerH, hcardker]
  have hlt : Nat.card (H.map φ) < m := by
    have hpos : 0 < Nat.card (H.map φ) := by
      rcases Nat.eq_zero_or_pos (Nat.card (H.map φ)) with h | h
      · rw [h, mul_zero] at hmul; exact absurd hmul hm0
      · exact h
    calc Nat.card (H.map φ) = 1 * Nat.card (H.map φ) := (one_mul _).symm
      _ < ℓ * Nat.card (H.map φ) := Nat.mul_lt_mul_of_pos_right hℓ.one_lt hpos
      _ = m := hmul.symm
  have hm' : ((Nat.card (H.map φ) : ℕ) : κ) ≠ 0 := by
    intro h; apply hm; rw [hmul]; push_cast; rw [h, mul_zero]
  have hgoal' : Goal E' (H.map φ) := ih _ hlt E' hE' (H.map φ) rfl hm'
  exact goal_of_step E E' H φ hφ hφs hkerH (fun V _ α hα h => hφuniv V α hα h) hgoal'

end SeparableQuotientInduction

end WeierstrassCurve

theorem solution
    {κ : Type*} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (E : WeierstrassCurve κ) [E.IsElliptic]
    (H : AddSubgroup (E.baseChange κ).toAffine.Point) (hH : ((Nat.card H : ℕ) : κ) ≠ 0) :
    ∃ (W : WeierstrassCurve κ) (_ : W.IsElliptic)
      (χ : (E.baseChange κ).toAffine.Point →+ (W.baseChange κ).toAffine.Point),
      χ ∈ WeierstrassCurve.rationalHomSet κ E W ∧ Function.Surjective χ ∧ χ.ker = H ∧
      ∀ (V : WeierstrassCurve κ) [V.IsElliptic]
        (α : (E.baseChange κ).toAffine.Point →+ (V.baseChange κ).toAffine.Point),
        α ∈ WeierstrassCurve.rationalHomSet κ E V → H ≤ α.ker →
        ∃ β ∈ WeierstrassCurve.rationalHomSet κ W V, α = β.comp χ :=
  WeierstrassCurve.SeparableQuotientInduction.goal_of_card_eq (Nat.card H) E inferInstance H rfl hH

end S_WeierstrassCurve_exists_mem_rationalHomSet_ker_eq_forall_exists_eq_comp
end P2MW
export P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_ker_eq_forall_exists_eq_comp (solution)
