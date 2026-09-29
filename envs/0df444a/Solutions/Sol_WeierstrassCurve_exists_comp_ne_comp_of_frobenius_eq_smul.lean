-- Prove2me | solution 1 for WeierstrassCurve.exists_comp_ne_comp_of_frobenius_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/3def924c-abd1-5041-ade5-696dc648da1d

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_DualIsogenyAPI
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_ker_eq_zmultiples_of_map_mem_zmultiples
import Theorems.Thm_WeierstrassCurve_finite_rationalHomSet_units
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_comp_ne_comp_of_frobenius_eq_smul
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"

namespace FrobeniusSmulNC

open AddSubgroup

variable {G : Type*} [AddCommGroup G]

theorem card_inf_ker_mul_card_map {H : Type*} [AddCommGroup H] (f : G →+ H) (T : AddSubgroup G) :
    Nat.card (f.ker ⊓ T : AddSubgroup G) * Nat.card (T.map f) = Nat.card T := by
  have h := AddSubgroup.relIndex_inf_mul_relIndex (⊥ : AddSubgroup G) f.ker T
  rw [bot_inf_eq, AddSubgroup.relIndex_bot_left, AddSubgroup.relIndex_bot_left,
    AddSubgroup.relIndex_ker] at h
  exact h

variable {ℓ : ℕ} (hℓ : ℓ.Prime) {T : AddSubgroup G} (hT : Nat.card T = ℓ ^ 2)
include hℓ hT

theorem finite_T : Finite T := Nat.finite_of_card_ne_zero (by rw [hT]; exact pow_ne_zero _ hℓ.ne_zero)

theorem eq_or_eq_of_line_le {A B : AddSubgroup G} (hA : Nat.card A = ℓ) (hAB : A ≤ B) (hBT : B ≤ T) :
    B = A ∨ B = T := by
  haveI := finite_T hℓ hT
  have hBfin : Finite B := Finite.of_injective (AddSubgroup.inclusion hBT) (AddSubgroup.inclusion_injective hBT)
  have h1 : Nat.card B ∣ ℓ ^ 2 := hT ▸ AddSubgroup.card_dvd_of_le hBT
  have h2 : ℓ ∣ Nat.card B := hA ▸ AddSubgroup.card_dvd_of_le hAB
  obtain ⟨i, hi, hBi⟩ := (Nat.dvd_prime_pow hℓ).1 h1
  interval_cases i
  · rw [hBi, pow_zero] at h2; exact absurd (Nat.le_of_dvd one_pos h2) (by have := hℓ.two_le; omega)
  · left; exact (AddSubgroup.eq_of_le_of_card_ge hAB (by rw [hA, hBi, pow_one])).symm
  · right; exact AddSubgroup.eq_of_le_of_card_ge hBT (by rw [hT, hBi])

omit hT in

theorem inf_eq_bot_of_ne {A B : AddSubgroup G} (hA : Nat.card A = ℓ) (hB : Nat.card B = ℓ) (hne : A ≠ B) :
    A ⊓ B = ⊥ := by
  have hAfin : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; exact hℓ.ne_zero)
  have hBfin : Finite B := Nat.finite_of_card_ne_zero (by rw [hB]; exact hℓ.ne_zero)
  have h1 : Nat.card (A ⊓ B : AddSubgroup G) ∣ ℓ := hA ▸ AddSubgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime hℓ).1 h1 with h | h
  · exact AddSubgroup.eq_bot_of_card_eq _ h
  · exfalso
    have hA' : A ⊓ B = A := AddSubgroup.eq_of_le_of_card_ge inf_le_left (by rw [hA, h])
    have hB' : A ⊓ B = B := AddSubgroup.eq_of_le_of_card_ge inf_le_right (by rw [hB, h])
    exact hne (hA'.symm.trans hB')

theorem sup_eq_of_ne {A B : AddSubgroup G} (hA : Nat.card A = ℓ) (hB : Nat.card B = ℓ) (hne : A ≠ B)
    (hAT : A ≤ T) (hBT : B ≤ T) : A ⊔ B = T := by
  rcases eq_or_eq_of_line_le hℓ hT hA le_sup_left (sup_le hAT hBT) with h | h
  · exfalso
    have hBA : B ≤ A := h ▸ le_sup_right
    have hAfin : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; exact hℓ.ne_zero)
    exact hne (AddSubgroup.eq_of_le_of_card_ge hBA (by rw [hA, hB])).symm
  · exact h

omit hT in
theorem exists_ne_zero_of_card {A : AddSubgroup G} (hA : Nat.card A = ℓ) : ∃ P ∈ A, P ≠ 0 := by
  rcases A.bot_or_exists_ne_zero with h | h
  · exfalso; rw [h, AddSubgroup.card_bot] at hA; exact hℓ.one_lt.ne hA
  · exact h

theorem inf_ker_eq_of_not_le {H : Type*} [AddCommGroup H] {α : G →+ H} {C : AddSubgroup G}
    (hC : Nat.card C = ℓ) (hCT : C ≤ T) (hCk : C ≤ α.ker) (hbad : ¬ T ≤ α.ker) :
    α.ker ⊓ T = C := by
  rcases eq_or_eq_of_line_le hℓ hT hC (le_inf hCk hCT) inf_le_right with h | h
  · exact h
  · exact absurd (h ▸ inf_le_left) hbad

theorem not_three_bad (α₁ α₂ α₃ : G →+ G) (C₁ C₂ C₃ : AddSubgroup G)
    (h12 : ∀ P, α₁ (α₂ P) = α₂ (α₁ P)) (h13 : ∀ P, α₁ (α₃ P) = α₃ (α₁ P))
    (hT₁ : ∀ P ∈ T, α₁ P ∈ T)
    (hC₁ : Nat.card C₁ = ℓ) (hC₂ : Nat.card C₂ = ℓ) (hC₃ : Nat.card C₃ = ℓ)
    (hC₁T : C₁ ≤ T) (hC₂T : C₂ ≤ T) (hC₃T : C₃ ≤ T)
    (n12 : C₁ ≠ C₂) (n13 : C₁ ≠ C₃) (n23 : C₂ ≠ C₃)
    (hk₁ : C₁ ≤ α₁.ker) (hk₂ : C₂ ≤ α₂.ker) (hk₃ : C₃ ≤ α₃.ker)
    (hb₁ : ¬ T ≤ α₁.ker) (hb₂ : ¬ T ≤ α₂.ker) (hb₃ : ¬ T ≤ α₃.ker) : False := by
  have K₁ := inf_ker_eq_of_not_le hℓ hT hC₁ hC₁T hk₁ hb₁
  have K₂ := inf_ker_eq_of_not_le hℓ hT hC₂ hC₂T hk₂ hb₂
  have K₃ := inf_ker_eq_of_not_le hℓ hT hC₃ hC₃T hk₃ hb₃

  have pres : ∀ (α' : G →+ G) (C' : AddSubgroup G), (∀ P, α₁ (α' P) = α' (α₁ P)) →
      α'.ker ⊓ T = C' → ∀ P ∈ C', α₁ P ∈ C' := by
    intro α' C' hc hK P hP
    rw [← hK] at hP ⊢
    refine ⟨?_, hT₁ P hP.2⟩
    have : α' P = 0 := hP.1
    show α' (α₁ P) = 0
    rw [← hc, this, map_zero]

  have inj : ∀ C' : AddSubgroup G, Nat.card C' = ℓ → C₁ ≠ C' → C' ≤ T →
      ∀ P ∈ C', α₁ P = 0 → P = 0 := by
    intro C' hC' hne hC'T P hP h0
    have hP1 : P ∈ C₁ := by rw [← K₁]; exact ⟨h0, hC'T hP⟩
    have : P ∈ C₁ ⊓ C' := ⟨hP1, hP⟩
    rw [inf_eq_bot_of_ne hℓ hC₁ hC' hne] at this
    exact this
  obtain ⟨P, hP, hP0⟩ := exists_ne_zero_of_card hℓ hC₁
  have hPT : P ∈ C₂ ⊔ C₃ := by rw [sup_eq_of_ne hℓ hT hC₂ hC₃ n23 hC₂T hC₃T]; exact hC₁T hP
  obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hPT
  have h0 : α₁ y + α₁ z = 0 := by rw [← map_add]; exact hk₁ hP
  have hy' : α₁ y ∈ C₂ := pres α₂ C₂ h12 K₂ y hy
  have hz' : α₁ z ∈ C₃ := pres α₃ C₃ h13 K₃ z hz
  have hyz : α₁ y ∈ C₂ ⊓ C₃ := by
    refine ⟨hy', ?_⟩
    have : α₁ y = -α₁ z := eq_neg_of_add_eq_zero_left h0
    rw [this]; exact C₃.neg_mem hz'
  rw [inf_eq_bot_of_ne hℓ hC₂ hC₃ n23] at hyz
  have hy0 : α₁ y = 0 := hyz
  have hz0 : α₁ z = 0 := by rwa [hy0, zero_add] at h0
  have := inj C₂ hC₂ n12 hC₂T y hy hy0
  have := inj C₃ hC₃ n13 hC₃T z hz hz0
  subst_vars
  exact hP0 (by simp)

theorem card_map_eq {H : Type*} [AddCommGroup H] {φ : G →+ H} {C : AddSubgroup G}
    (hC : Nat.card C = ℓ) (hK : φ.ker ⊓ T = C) : Nat.card (T.map φ) = ℓ := by
  have h := card_inf_ker_mul_card_map φ T
  rw [hK, hC, hT, pow_two] at h
  exact Nat.eq_of_mul_eq_mul_left hℓ.pos h

omit hℓ hT in

theorem eq_zero_of_zsmul_eq_zero {X : Type*} [AddCommGroup X] (hdiv : ∀ P : G, ∃ P', P = (ℓ : ℤ) • P')
    (E : G →+ X) (h : ∀ P, (ℓ : ℤ) • E P = 0) : ∀ P, E P = 0 := by
  intro P
  obtain ⟨P', rfl⟩ := hdiv P
  rw [map_zsmul]; exact h P'

end FrobeniusSmulNC

namespace FrobeniusSmulNC

open AddSubgroup

theorem core {G H : Type*} [AddCommGroup G] [AddCommGroup H] {ℓ : ℕ} (hℓ : ℓ.Prime)
    {T : AddSubgroup G} (hT : Nat.card T = ℓ ^ 2) (hTdef : ∀ P, P ∈ T ↔ (ℓ : ℤ) • P = 0)
    (S : Set (G →+ G)) (hS : ∀ α ∈ S, ∀ β ∈ S, ∀ P, α (β P) = β (α P))
    (U : Set (G →+ G)) (hU : U.Finite)
    (hUdef : ∀ u ∈ S, ∀ v ∈ S, (∀ P, u (v P) = P) → (∀ P, v (u P) = P) → u ∈ U)
    (hdiv : ∀ P : G, ∃ P', P = (ℓ : ℤ) • P')
    (hdivS : ∀ α ∈ S, (∀ P ∈ T, α P = 0) → ∃ β ∈ S, ∀ P, α P = (ℓ : ℤ) • β P)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : ι → (G →+ H)) (ψ : ι → (H →+ G)) (C : ι → AddSubgroup G)
    (hC : ∀ i, Nat.card (C i) = ℓ) (hCT : ∀ i, C i ≤ T) (hCinj : Function.Injective C)
    (hker : ∀ i, (φ i).ker = C i)
    (hdual : ∀ i P, ψ i (φ i P) = (ℓ : ℤ) • P) (hdual' : ∀ i R, φ i (ψ i R) = (ℓ : ℤ) • R)
    (hcompS : ∀ i j, (ψ i).comp (φ j) ∈ S)
    (hsurj : ∀ i, Function.Surjective (φ i))
    (hcard : hU.toFinset.card + 3 ≤ Fintype.card ι) : False := by
  classical
  haveI : Finite T := finite_T hℓ hT

  have hne : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨i₀⟩ := hne
  set α : ι → (G →+ G) := fun j => (ψ i₀).comp (φ j) with hα_def
  have hα : ∀ j P, α j P = ψ i₀ (φ j P) := fun j P => rfl
  have hαS : ∀ j, α j ∈ S := fun j => hcompS i₀ j
  have hαT : ∀ j, ∀ P ∈ T, α j P ∈ T := by
    intro j P hP
    rw [hTdef] at hP ⊢
    rw [← map_zsmul, hP, map_zero]
  have hCk : ∀ j, C j ≤ (α j).ker := by
    intro j P hP
    rw [← hker] at hP
    show ψ i₀ (φ j P) = 0
    rw [show φ j P = 0 from hP, map_zero]
  have hK : ∀ j, (φ j).ker ⊓ T = C j := fun j => by rw [hker]; exact inf_eq_left.2 (hCT j)

  set bad : Finset ι := Finset.univ.filter (fun j => ¬ T ≤ (α j).ker) with hbad_def
  have hbad : bad.card ≤ 2 := by
    by_contra h
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Finset.two_lt_card_iff (s := bad)).1 (by omega)
    rw [hbad_def, Finset.mem_filter] at ha hb hc
    replace ha := ha.2; replace hb := hb.2; replace hc := hc.2
    exact not_three_bad hℓ hT (α a) (α b) (α c) (C a) (C b) (C c)
      (hS _ (hαS a) _ (hαS b)) (hS _ (hαS a) _ (hαS c)) (hαT a)
      (hC a) (hC b) (hC c) (hCT a) (hCT b) (hCT c)
      (hCinj.ne hab) (hCinj.ne hac) (hCinj.ne hbc)
      (hCk a) (hCk b) (hCk c) ha hb hc
  set good : Finset ι := Finset.univ.filter (fun j => T ≤ (α j).ker) with hgood_def
  have hgb : good.card + bad.card = Fintype.card ι := by
    rw [hgood_def, hbad_def]
    exact Finset.card_filter_add_card_filter_not _
  have hgood_card : hU.toFinset.card + 1 ≤ good.card := by omega
  have hgood : ∀ j ∈ good, ∀ P ∈ T, α j P = 0 := by
    intro j hj P hP
    simp only [hgood_def, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact hj hP

  have himc : ∀ j, Nat.card (T.map (φ j)) = ℓ := fun j => card_map_eq hℓ hT (hC j) (hK j)
  have hker₀ : ∀ i R, ψ i R = 0 → R ∈ T.map (φ i) := by
    intro i R hR
    obtain ⟨P, rfl⟩ := hsurj i R
    refine ⟨P, ?_, rfl⟩
    rw [SetLike.mem_coe, hTdef, ← hdual i P, hR]
  have him_eq : ∀ j ∈ good, T.map (φ j) = T.map (φ i₀) := by
    intro j hj
    haveI : Finite (T.map (φ i₀)) :=
      Nat.finite_of_card_ne_zero (by rw [himc]; exact hℓ.ne_zero)
    refine AddSubgroup.eq_of_le_of_card_ge ?_ (by rw [himc, himc])
    rintro R ⟨P, hP, rfl⟩
    exact hker₀ i₀ _ (hgood j hj P hP)

  have hgood' : ∀ j ∈ good, ∀ P ∈ T, ψ j (φ i₀ P) = 0 := by
    intro j hj P hP
    have : φ i₀ P ∈ T.map (φ j) := by rw [him_eq j hj]; exact ⟨P, hP, rfl⟩
    obtain ⟨P', hP', hPP'⟩ := this
    rw [← hPP', hdual, ← hTdef]; exact hP'

  choose β hβS hβ using fun j : good => hdivS (α j) (hαS j) (hgood j j.2)
  choose β' hβ'S hβ' using fun j : good =>
    hdivS ((ψ j).comp (φ i₀)) (hcompS j i₀) (hgood' j j.2)
  have hkill2 : ∀ (E : G →+ G), (∀ P, (ℓ : ℤ) • ((ℓ : ℤ) • E P) = 0) → ∀ P, E P = 0 := by
    intro E hE
    apply eq_zero_of_zsmul_eq_zero hdiv
    intro P
    obtain ⟨P', rfl⟩ := hdiv P
    rw [map_zsmul]; exact hE P'
  have hunit₁ : ∀ j : good, ∀ P, β' j (β j P) = P := by
    intro j P
    have h := hkill2 ((β' j).comp (β j) - AddMonoidHom.id _) ?_ P
    · simpa [sub_eq_zero] using h
    intro Q
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, AddMonoidHom.id_apply, smul_sub]
    rw [sub_eq_zero, ← map_zsmul, ← hβ j Q, ← hβ' j, hα]
    show ψ j (φ i₀ (ψ i₀ (φ j Q))) = _
    rw [hdual', map_zsmul, hdual]
  have hunit₂ : ∀ j : good, ∀ P, β j (β' j P) = P := by
    intro j P
    have h := hkill2 ((β j).comp (β' j) - AddMonoidHom.id _) ?_ P
    · simpa [sub_eq_zero] using h
    intro Q
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, AddMonoidHom.id_apply, smul_sub]
    rw [sub_eq_zero, ← map_zsmul, ← hβ' j Q, AddMonoidHom.comp_apply, ← hβ j, hα]
    rw [hdual', map_zsmul, hdual]
  have hβU : ∀ j : good, β j ∈ U := fun j =>
    hUdef _ (hβS j) _ (hβ'S j) (hunit₂ j) (hunit₁ j)

  have hφβ : ∀ j : good, ∀ P, φ (j : ι) P = φ i₀ (β j P) := by
    intro j
    have h := eq_zero_of_zsmul_eq_zero hdiv (φ (j : ι) - (φ i₀).comp (β j)) ?_
    · intro P; simpa [sub_eq_zero] using h P
    intro Q
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, smul_sub]
    rw [sub_eq_zero, ← map_zsmul (φ i₀), ← hβ j Q, hα, hdual']
  have hinj : Function.Injective (fun j : good => (⟨β j, hU.mem_toFinset.2 (hβU j)⟩ : hU.toFinset)) := by
    intro j j' hjj'
    simp only [Subtype.mk.injEq] at hjj'
    have hφ : φ (j : ι) = φ (j' : ι) := by
      ext P; rw [hφβ j, hφβ j', hjj']
    have : C j = C j' := by rw [← hker, ← hker, hφ]
    exact Subtype.ext (hCinj this)
  have h1 := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_coe, Fintype.card_coe] at h1
  omega

theorem exists_lines {G : Type*} [AddCommGroup G] {ℓ : ℕ} (hℓ : ℓ.Prime)
    {T : AddSubgroup G} (hT : Nat.card T = ℓ ^ 2) (hTdef : ∀ P, P ∈ T ↔ (ℓ : ℤ) • P = 0)
    (n : ℕ) (hn : n ≤ ℓ) :
    ∃ Q : Fin n → G, (∀ i, Q i ∈ T) ∧ (∀ i, addOrderOf (Q i) = ℓ) ∧
      Function.Injective (fun i => AddSubgroup.zmultiples (Q i)) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Finite T := finite_T hℓ hT
  have hord : ∀ P ∈ T, P ≠ 0 → addOrderOf P = ℓ := by
    intro P hP hP0
    refine addOrderOf_eq_prime ?_ hP0
    rw [← natCast_zsmul]; exact (hTdef P).1 hP

  obtain ⟨P₁, hP₁T, hP₁0⟩ : ∃ P ∈ T, P ≠ 0 := by
    rcases T.bot_or_exists_ne_zero with h | h
    · exfalso; rw [h, AddSubgroup.card_bot] at hT
      have := hℓ.one_lt; nlinarith
    · exact h
  have hP₁ord := hord P₁ hP₁T hP₁0
  have hL₁card : Nat.card (AddSubgroup.zmultiples P₁) = ℓ := by rw [Nat.card_zmultiples, hP₁ord]
  have hL₁T : AddSubgroup.zmultiples P₁ ≤ T := AddSubgroup.zmultiples_le_of_mem hP₁T

  obtain ⟨P₂, hP₂T, hP₂L⟩ : ∃ P ∈ T, P ∉ AddSubgroup.zmultiples P₁ := by
    refine SetLike.exists_of_lt (lt_of_le_of_ne hL₁T ?_)
    intro h
    have := hL₁card; rw [h, hT, pow_two] at this
    exact hℓ.one_lt.ne' (by simpa [hℓ.ne_zero] using this)
  refine ⟨fun i => P₂ + ((i : ℕ) : ℤ) • P₁, fun i => T.add_mem hP₂T (T.zsmul_mem hP₁T _), ?_, ?_⟩
  · intro i
    refine hord _ (T.add_mem hP₂T (T.zsmul_mem hP₁T _)) ?_
    intro h
    apply hP₂L
    have : P₂ = -(((i : ℕ) : ℤ) • P₁) := eq_neg_of_add_eq_zero_left h
    rw [this]; exact (AddSubgroup.zmultiples P₁).neg_mem (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) _)
  · intro i j hij
    simp only at hij
    by_contra hne
    have hQcard : ∀ m : Fin n, Nat.card (AddSubgroup.zmultiples (P₂ + ((m : ℕ) : ℤ) • P₁)) = ℓ := by
      intro m
      rw [Nat.card_zmultiples]
      refine hord _ (T.add_mem hP₂T (T.zsmul_mem hP₁T _)) ?_
      intro h
      apply hP₂L
      have : P₂ = -(((m : ℕ) : ℤ) • P₁) := eq_neg_of_add_eq_zero_left h
      rw [this]; exact (AddSubgroup.zmultiples P₁).neg_mem (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) _)

    set D : G := (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) • P₁ with hD_def
    have hDeq : D = (P₂ + ((i : ℕ) : ℤ) • P₁) - (P₂ + ((j : ℕ) : ℤ) • P₁) := by
      rw [hD_def, sub_zsmul]; abel
    have hD₁ : D ∈ AddSubgroup.zmultiples P₁ := AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) _
    have hD₂ : D ∈ AddSubgroup.zmultiples (P₂ + ((i : ℕ) : ℤ) • P₁) := by
      rw [hDeq]
      refine AddSubgroup.sub_mem _ (AddSubgroup.mem_zmultiples _) ?_
      rw [hij]; exact AddSubgroup.mem_zmultiples _
    have hD0 : D ≠ 0 := by
      intro h0
      rw [hD_def, ← addOrderOf_dvd_iff_zsmul_eq_zero, hP₁ord] at h0
      have habs : |(((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))| < (ℓ : ℤ) := by
        rw [abs_sub_lt_iff]; constructor <;> omega
      have := Int.eq_zero_of_abs_lt_dvd h0 habs
      exact hne (Fin.ext (by omega))

    have hLeq : AddSubgroup.zmultiples P₁ = AddSubgroup.zmultiples (P₂ + ((i : ℕ) : ℤ) • P₁) := by
      by_contra hne'
      have := inf_eq_bot_of_ne hℓ hL₁card (hQcard i) hne'
      have hmem : D ∈ AddSubgroup.zmultiples P₁ ⊓ AddSubgroup.zmultiples (P₂ + ((i : ℕ) : ℤ) • P₁) :=
        ⟨hD₁, hD₂⟩
      rw [this] at hmem
      exact hD0 hmem
    apply hP₂L
    have hmem : P₂ + ((i : ℕ) : ℤ) • P₁ ∈ AddSubgroup.zmultiples P₁ := by
      rw [hLeq]; exact AddSubgroup.mem_zmultiples _
    have := (AddSubgroup.zmultiples P₁).sub_mem hmem
      (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples P₁) ((i : ℕ) : ℤ))
    simpa using this

theorem natCast_ne_zero_of_prime_gt {R : Type*} [NonAssocRing R] [Nontrivial R] {p : ℕ}
    (hp : p.Prime) (hgt : ringChar R < p) : (p : R) ≠ 0 := by
  intro h
  have hd : ringChar R ∣ p := (ringChar.spec R p).1 h
  rcases (Nat.dvd_prime hp).1 hd with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · omega

end FrobeniusSmulNC

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution {F : Type*} [Field F] [Fintype F] (k : Type*) [Field k] [DecidableEq k] [Algebra F k] [IsAlgClosed k] [Algebra.IsAlgebraic F k] (W : WeierstrassCurve F) [W.IsElliptic] (σ : k →ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) (a : ℤ) (ha : ∀ P : (W⁄k).Point, WeierstrassCurve.Affine.Point.map (W' := W) σ P = a • P) : ∃ α ∈ WeierstrassCurve.rationalHomSet k W W, ∃ β ∈ WeierstrassCurve.rationalHomSet k W W, α.comp β ≠ β.comp α := by
  classical
  by_contra hH
  push Not at hH

  have hUfin := WeierstrassCurve.finite_rationalHomSet_units k W
  set U := {u : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point |
      u ∈ WeierstrassCurve.rationalHomSet k W W ∧ ∃ v ∈ WeierstrassCurve.rationalHomSet k W W,
        u.comp v = AddMonoidHom.id _ ∧ v.comp u = AddMonoidHom.id _} with hU_def

  haveI : Finite (WeierstrassCurve F) :=
    Finite.of_injective (fun V : WeierstrassCurve F => (V.a₁, V.a₂, V.a₃, V.a₄, V.a₆))
      (fun V V' h => by
        simp only [Prod.mk.injEq] at h
        exact WeierstrassCurve.ext h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
  letI : Fintype (WeierstrassCurve F) := Fintype.ofFinite _
  set B := hUfin.toFinset.card with hB_def
  set c := Fintype.card (WeierstrassCurve F) with hc_def

  obtain ⟨ℓ, hℓge, hℓ⟩ := Nat.exists_infinite_primes (c * (B + 3) + ringChar F + 3)
  have hℓF : (ℓ : F) ≠ 0 := FrobeniusSmulNC.natCast_ne_zero_of_prime_gt hℓ (by omega)
  have hℓk : (ℓ : k) ≠ 0 := by
    rw [← map_natCast (algebraMap F k)]; exact (map_ne_zero _).2 hℓF
  have hℓ2 : ℓ ≠ 2 := by omega
  haveI : Fact ℓ.Prime := ⟨hℓ⟩

  set T : AddSubgroup (W.baseChange k).toAffine.Point :=
    (Submodule.torsionBy ℤ (W.baseChange k).toAffine.Point (ℓ : ℤ)).toAddSubgroup with hT_def
  have hTdef : ∀ P, P ∈ T ↔ (ℓ : ℤ) • P = 0 := fun P => Submodule.mem_torsionBy_iff _ _
  have hT : Nat.card T = ℓ ^ 2 := WeierstrassCurve.card_torsion_of_isAlgClosed W hℓk
  haveI : Finite T := FrobeniusSmulNC.finite_T hℓ hT

  obtain ⟨Q, hQT, hQord, hQinj⟩ :=
    FrobeniusSmulNC.exists_lines hℓ hT hTdef (c * (B + 3) + 1) (by omega)

  have hA : ∀ i, ∃ V : WeierstrassCurve F, V.IsElliptic ∧
      ∃ φ ∈ WeierstrassCurve.rationalHomSet k W V, ∃ ψ ∈ WeierstrassCurve.rationalHomSet k V W,
        φ.ker = AddSubgroup.zmultiples (Q i) ∧ AddMonoidHom.IsDualPair φ ψ (ℓ : ℤ) := fun i =>
    WeierstrassCurve.exists_mem_rationalHomSet_ker_eq_zmultiples_of_map_mem_zmultiples k W σ hσ
      hℓ hℓ2 hℓF (Q i) (hQord i)
      (by rw [ha]; exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) a)
  choose V hV using hA

  obtain ⟨V₀, hV₀⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card V (n := B + 2)
    (by rw [Fintype.card_fin, ← hc_def]; nlinarith)
  set J : Finset (Fin (c * (B + 3) + 1)) := Finset.univ.filter (fun i => V i = V₀) with hJ_def
  have hJcard : B + 2 < J.card := hV₀
  have hJmem : ∀ i ∈ J, V i = V₀ := fun i hi => (Finset.mem_filter.1 hi).2
  have hJne : J.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨j₀, hj₀⟩ := hJne
  haveI hV₀ell : V₀.IsElliptic := hJmem j₀ hj₀ ▸ (hV j₀).1
  have hJ : ∀ i ∈ J, ∃ φ ∈ WeierstrassCurve.rationalHomSet k W V₀,
      ∃ ψ ∈ WeierstrassCurve.rationalHomSet k V₀ W,
        φ.ker = AddSubgroup.zmultiples (Q i) ∧ AddMonoidHom.IsDualPair φ ψ (ℓ : ℤ) := by
    intro i hi
    have h := (hV i).2
    rw [hJmem i hi] at h
    exact h
  choose φ hφS ψ hψS hker hdual using fun i : J => hJ i i.2
  let i₀ : J := ⟨j₀, hj₀⟩

  have hexists : ∃ P : (W.baseChange k).toAffine.Point, (ℓ : ℤ) • P ≠ 0 := by
    by_contra hall
    push Not at hall
    obtain ⟨ℓ', hℓ'ge, hℓ'⟩ := Nat.exists_infinite_primes (ℓ ^ 2 + ringChar F + 2)
    have hℓ'F : (ℓ' : F) ≠ 0 := FrobeniusSmulNC.natCast_ne_zero_of_prime_gt hℓ' (by omega)
    have hℓ'k : (ℓ' : k) ≠ 0 := by
      rw [← map_natCast (algebraMap F k)]; exact (map_ne_zero _).2 hℓ'F
    have hT' : Nat.card (Submodule.torsionBy ℤ (W.baseChange k).toAffine.Point (ℓ' : ℤ)).toAddSubgroup
        = ℓ' ^ 2 := WeierstrassCurve.card_torsion_of_isAlgClosed W hℓ'k
    have hle : (Submodule.torsionBy ℤ (W.baseChange k).toAffine.Point (ℓ' : ℤ)).toAddSubgroup ≤ T :=
      fun P _ => (hTdef P).2 (hall P)
    have h := AddSubgroup.card_le_of_le hle
    rw [hT', hT] at h
    nlinarith [hℓ'.two_le]
  have hmulS : (ψ i₀).comp (φ i₀) ∈ WeierstrassCurve.rationalHomSet k W W :=
    WeierstrassCurve.comp_mem_rationalHomSet k W V₀ W (hφS i₀) (hψS i₀)
  have hmul_ne : (ψ i₀).comp (φ i₀) ≠ 0 := by
    obtain ⟨P, hP⟩ := hexists
    intro h0
    apply hP
    rw [← (hdual i₀).comp_left P]
    show ((ψ i₀).comp (φ i₀)) P = 0
    rw [h0, AddMonoidHom.zero_apply]
  have hdiv : ∀ P : (W.baseChange k).toAffine.Point, ∃ P', P = (ℓ : ℤ) • P' := by
    intro P
    obtain ⟨P', hP'⟩ := WeierstrassCurve.surjective_of_mem_rationalHomSet k hmulS hmul_ne P
    exact ⟨P', by rw [← hP']; exact (hdual i₀).comp_left P'⟩

  have hφne : ∀ i : J, φ i ≠ 0 := by
    intro i h0
    have hk : (φ i).ker = ⊤ := by rw [h0]; exact AddMonoidHom.ker_zero
    rw [hker i] at hk
    haveI : Finite (AddSubgroup.zmultiples (Q i)) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zmultiples, hQord]; exact hℓ.ne_zero)
    have h := AddSubgroup.card_le_of_le (show T ≤ AddSubgroup.zmultiples (Q (i : Fin _)) from
      hk ▸ le_top)
    rw [hT, Nat.card_zmultiples, hQord, pow_two] at h
    have := hℓ.one_lt
    nlinarith
  have hsurj : ∀ i : J, Function.Surjective (φ i) := fun i =>
    WeierstrassCurve.surjective_of_mem_rationalHomSet k (hφS i) (hφne i)

  have hdivS : ∀ α ∈ WeierstrassCurve.rationalHomSet k W W, (∀ P ∈ T, α P = 0) →
      ∃ β ∈ WeierstrassCurve.rationalHomSet k W W, ∀ P, α P = (ℓ : ℤ) • β P :=
    fun α hα h => WeierstrassCurve.exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero k W W
      hℓF hα (fun P hP => h P ((hTdef P).2 hP))

  refine FrobeniusSmulNC.core hℓ hT hTdef (WeierstrassCurve.rationalHomSet k W W)
    (fun α hα β hβ P => ?_) U hUfin (fun u hu v hv h1 h2 => ?_) hdiv hdivS (ι := J) φ ψ
    (fun i => AddSubgroup.zmultiples (Q i)) (fun i => by rw [Nat.card_zmultiples, hQord])
    (fun i => AddSubgroup.zmultiples_le_of_mem (hQT i))
    (fun i j h => Subtype.ext (hQinj h)) hker
    (fun i => (hdual i).comp_left) (fun i => (hdual i).comp_right)
    (fun i j => WeierstrassCurve.comp_mem_rationalHomSet k W V₀ W (hφS j) (hψS i)) hsurj ?_
  · have := hH α hα β hβ
    exact DFunLike.congr_fun this P
  · exact ⟨hu, v, hv, AddMonoidHom.ext h1, AddMonoidHom.ext h2⟩
  · rw [Fintype.card_coe]; omega

end S_WeierstrassCurve_exists_comp_ne_comp_of_frobenius_eq_smul
end P2MW
export P2MW.S_WeierstrassCurve_exists_comp_ne_comp_of_frobenius_eq_smul (solution)
