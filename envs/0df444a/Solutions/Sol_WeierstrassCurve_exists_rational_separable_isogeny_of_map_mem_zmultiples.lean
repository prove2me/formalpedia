-- Prove2me | solution 1 for WeierstrassCurve.exists_rational_separable_isogeny_of_map_mem_zmultiples
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/d18afdfb-f27f-5a4b-8ba3-db1b3b2e617f

import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Theorems.Thm_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet
import Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq
import Theorems.Thm_WeierstrassCurve_isOddVeluSet_oddOrderSummingSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_rational_separable_isogeny_of_map_mem_zmultiples
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.vcInvEmbedding_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"

open Polynomial

noncomputable section

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine a₃ a₁ map map_b₂ b₂ isElliptic_iff Ψ₂Sq a₄ a₂ a₆ toAffine Affine.Point map_Δ map_a₆ Affine.Point.map map_a₁ map_a₄ Affine.Point.some_ne_zero Δ Affine.equation_iff Affine.Point.map_some Affine.Point.neg_some map_a₂ map_Ψ₂Sq baseChange j b₄ map_a₃ veluGx veluGy veluT veluU veluW veluT_eq veluU_eq_Ψ₂Sq_eval veluTSum veluWSum veluQuotient IsOddVeluSet veluX veluY Affine.Point.coordsOrZero_some oddOrderSummingSet mem_oddOrderSummingSet exists_veluPointHom_oddOrderSummingSet veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq isOddVeluSet_oddOrderSummingSet"
namespace FrobVeluDescent
p2m_open "WeierstrassCurve"

section Descent

variable {F : Type*} [Field F] [Fintype F] {k : Type*} [Field k] [Algebra F k]

theorem mem_range_algebraMap_of_pow_card_eq {a : k} (ha : a ^ Fintype.card F = a) :
    a ∈ Set.range (algebraMap F k) := by
  classical
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  set f : k[X] := X ^ Fintype.card F - X with hf
  have hf0 : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k hq
  have hsub : Finset.univ.image (algebraMap F k) ⊆ f.roots.toFinset := by
    intro b hb
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hb
    rw [Multiset.mem_toFinset, mem_roots hf0, IsRoot.def, eval_sub, eval_pow, eval_X, ← map_pow,
      FiniteField.pow_card, sub_self]
  have hcard : f.roots.toFinset.card ≤ (Finset.univ.image (algebraMap F k)).card := by
    rw [Finset.card_image_of_injective _ (algebraMap F k).injective, Finset.card_univ]
    calc f.roots.toFinset.card ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
      _ ≤ f.natDegree := card_roots' f
      _ = Fintype.card F := FiniteField.X_pow_card_sub_X_natDegree_eq k hq
  have hT := Finset.eq_of_subset_of_card_le hsub hcard
  have ha' : a ∈ f.roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hf0, IsRoot.def, eval_sub, eval_pow, eval_X, ha, sub_self]
  rw [← hT, Finset.mem_image] at ha'
  obtain ⟨c, -, hc⟩ := ha'
  exact ⟨c, hc⟩

variable (σ : k →ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F)
include hσ

theorem mem_range_of_fixed {a : k} (ha : σ a = a) : a ∈ Set.range (algebraMap F k) :=
  mem_range_algebraMap_of_pow_card_eq (by rw [← hσ, ha])

theorem lifts_of_map_eq {p : k[X]} (hp : p.map (σ : k →+* k) = p) :
    p ∈ lifts (algebraMap F k) := by
  rw [lifts_iff_coeff_lifts]
  intro n
  apply mem_range_of_fixed σ hσ
  have := congr_arg (fun q => q.coeff n) hp
  simpa only [coeff_map, RingHom.coe_coe] using this

end Descent

section Poly

variable {k : Type*} [Field k] (Xs : Finset k)

def D : k[X] := ∏ ξ ∈ Xs, (X - C ξ)

theorem monic_D : (D Xs).Monic := monic_prod_of_monic _ _ fun ξ _ => monic_X_sub_C ξ

theorem natDegree_D : (D Xs).natDegree = Xs.card := by
  rw [D, natDegree_prod_of_monic _ _ fun ξ _ => monic_X_sub_C ξ]
  simp

theorem eval_D (x : k) : (D Xs).eval x = ∏ ξ ∈ Xs, (x - ξ) := by
  simp only [D, eval_prod, eval_sub, eval_X, eval_C]

theorem eval_D_ne_zero {x : k} (hx : x ∉ Xs) : (D Xs).eval x ≠ 0 := by
  rw [eval_D]
  exact Finset.prod_ne_zero_iff.mpr fun ξ hξ => sub_ne_zero.mpr fun h => hx (h ▸ hξ)

theorem eval_D_eq_zero {ξ : k} (hξ : ξ ∈ Xs) : (D Xs).eval ξ = 0 := by
  rw [eval_D]
  exact Finset.prod_eq_zero hξ (sub_self ξ)

variable [DecidableEq k] (t u A : k → k) (a₁ a₃ : k)

def E (ξ : k) : k[X] := ∏ ξ' ∈ Xs.erase ξ, (X - C ξ')

def Pk : k[X] := X * D Xs ^ 2 + ∑ ξ ∈ Xs, (C (t ξ) * (X - C ξ) + C (u ξ)) * E Xs ξ ^ 2

def M1 (ξ : k) : k[X] := (C (2 * u ξ) + C (t ξ) * (X - C ξ)) * E Xs ξ ^ 3

def M0 (ξ : k) : k[X] :=
  (C (u ξ) * (C a₁ * X + C a₃) + (C (a₁ * t ξ) * (X - C ξ) + C (A ξ)) * (X - C ξ)) * E Xs ξ ^ 3

def N1 : k[X] := D Xs ^ 3 - ∑ ξ ∈ Xs, M1 Xs t u ξ

def N0 : k[X] := -∑ ξ ∈ Xs, M0 Xs t u A a₁ a₃ ξ

theorem monic_E (ξ : k) : (E Xs ξ).Monic := monic_prod_of_monic _ _ fun ξ _ => monic_X_sub_C ξ

theorem natDegree_E {ξ : k} (hξ : ξ ∈ Xs) : (E Xs ξ).natDegree = Xs.card - 1 := by
  rw [E, natDegree_prod_of_monic _ _ fun ξ _ => monic_X_sub_C ξ]
  simp [Finset.card_erase_of_mem hξ]

theorem natDegree_tail_lt :
    (∑ ξ ∈ Xs, (C (t ξ) * (X - C ξ) + C (u ξ)) * E Xs ξ ^ 2).natDegree <
      (X * D Xs ^ 2 : k[X]).natDegree := by
  rw [monic_X.natDegree_mul ((monic_D Xs).pow 2), natDegree_X, natDegree_pow, natDegree_D]
  have hle : (∑ ξ ∈ Xs, (C (t ξ) * (X - C ξ) + C (u ξ)) * E Xs ξ ^ 2).natDegree ≤
      2 * Xs.card - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun ξ hξ => ?_
    have hcard : 1 ≤ Xs.card := Finset.card_pos.mpr ⟨ξ, hξ⟩
    calc ((C (t ξ) * (X - C ξ) + C (u ξ)) * E Xs ξ ^ 2).natDegree
        ≤ (C (t ξ) * (X - C ξ) + C (u ξ)).natDegree + (E Xs ξ ^ 2).natDegree := natDegree_mul_le
      _ ≤ 1 + 2 * (Xs.card - 1) := by
          gcongr
          · exact (natDegree_add_le _ _).trans
              (max_le ((natDegree_C_mul_le _ _).trans (natDegree_X_sub_C ξ).le) (by simp))
          · rw [natDegree_pow, natDegree_E Xs hξ]
      _ = 2 * Xs.card - 1 := by omega
  omega

theorem monic_Pk : (Pk Xs t u).Monic :=
  (monic_X.mul ((monic_D Xs).pow 2)).add_of_left (degree_lt_degree (natDegree_tail_lt Xs t u))

theorem natDegree_Pk : (Pk Xs t u).natDegree = (D Xs ^ 2).natDegree + 1 := by
  rw [Pk, natDegree_add_eq_left_of_natDegree_lt (natDegree_tail_lt Xs t u),
    monic_X.natDegree_mul ((monic_D Xs).pow 2), natDegree_X]
  ring

theorem eval_E_mul {ξ : k} (hξ : ξ ∈ Xs) (x : k) :
    (E Xs ξ).eval x * (x - ξ) = (D Xs).eval x := by
  simp only [E, eval_D, eval_prod, eval_sub, eval_X, eval_C]
  exact Finset.prod_erase_mul Xs (fun ξ' => x - ξ') hξ

theorem eval_E_self_ne_zero (ξ : k) : (E Xs ξ).eval ξ ≠ 0 := by
  simp only [E, eval_prod, eval_sub, eval_X, eval_C]
  exact Finset.prod_ne_zero_iff.mpr fun ξ' hξ' => sub_ne_zero.mpr (Finset.ne_of_mem_erase hξ').symm

theorem eval_E_of_ne {ξ ξ₀ : k} (hξ₀ : ξ₀ ∈ Xs) (hne : ξ ≠ ξ₀) : (E Xs ξ).eval ξ₀ = 0 := by
  simp only [E, eval_prod, eval_sub, eval_X, eval_C]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne.symm, hξ₀⟩) (sub_self ξ₀)

theorem eval_Pk_self {ξ₀ : k} (hξ₀ : ξ₀ ∈ Xs) :
    (Pk Xs t u).eval ξ₀ = u ξ₀ * (E Xs ξ₀).eval ξ₀ ^ 2 := by
  simp only [Pk, eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_sub, eval_finsetSum,
    eval_D_eq_zero Xs hξ₀]
  rw [Finset.sum_eq_single_of_mem ξ₀ hξ₀ fun ξ _ hne => by rw [eval_E_of_ne Xs hξ₀ hne]; ring]
  ring

theorem isCoprime_Pk (hu : ∀ ξ ∈ Xs, u ξ ≠ 0) : IsCoprime (Pk Xs t u) (D Xs ^ 2) := by
  refine IsCoprime.pow_right ?_
  rw [D]
  refine IsCoprime.prod_right fun ξ hξ => ((irreducible_X_sub_C ξ).coprime_iff_not_dvd.mpr ?_).symm
  rw [dvd_iff_isRoot, IsRoot.def, eval_Pk_self Xs t u hξ]
  exact mul_ne_zero (hu ξ hξ) (pow_ne_zero _ (eval_E_self_ne_zero Xs ξ))

theorem eval_Pk_div {x : k} (hx : x ∉ Xs) :
    (Pk Xs t u).eval x / (D Xs).eval x ^ 2 =
      x + ∑ ξ ∈ Xs, (t ξ / (x - ξ) + u ξ / (x - ξ) ^ 2) := by
  have hd := eval_D_ne_zero Xs hx
  rw [div_eq_iff (pow_ne_zero 2 hd), add_mul, Finset.sum_mul]
  simp only [Pk, eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_sub, eval_finsetSum]
  congr 1
  refine Finset.sum_congr rfl fun ξ hξ => ?_
  have hxξ : x - ξ ≠ 0 := sub_ne_zero.mpr fun h => hx (h ▸ hξ)
  rw [← eval_E_mul Xs hξ, div_add_div _ _ hxξ (pow_ne_zero 2 hxξ),
    div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hxξ (pow_ne_zero 2 hxξ))]
  ring

theorem eval_N_div {x : k} (hx : x ∉ Xs) (y : k) :
    ((N0 Xs t u A a₁ a₃).eval x + (N1 Xs t u).eval x * y) / (D Xs).eval x ^ 3 =
      y - ∑ ξ ∈ Xs, (u ξ * (2 * y + a₁ * x + a₃) / (x - ξ) ^ 3 +
        (t ξ * (a₁ * (x - ξ) + y) + A ξ) / (x - ξ) ^ 2) := by
  have hd := eval_D_ne_zero Xs hx
  have key : ∀ ξ ∈ Xs, (M0 Xs t u A a₁ a₃ ξ).eval x + (M1 Xs t u ξ).eval x * y =
      (u ξ * (2 * y + a₁ * x + a₃) / (x - ξ) ^ 3 +
        (t ξ * (a₁ * (x - ξ) + y) + A ξ) / (x - ξ) ^ 2) * (D Xs).eval x ^ 3 := by
    intro ξ hξ
    have hxξ : x - ξ ≠ 0 := sub_ne_zero.mpr fun h => hx (h ▸ hξ)
    rw [← eval_E_mul Xs hξ, div_add_div _ _ (pow_ne_zero 3 hxξ) (pow_ne_zero 2 hxξ),
      div_mul_eq_mul_div, eq_div_iff (mul_ne_zero (pow_ne_zero 3 hxξ) (pow_ne_zero 2 hxξ))]
    simp only [M0, M1, eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_sub]
    ring
  rw [div_eq_iff (pow_ne_zero 3 hd), sub_mul, Finset.sum_mul, ← Finset.sum_congr rfl key,
    Finset.sum_add_distrib, ← Finset.sum_mul]
  simp only [N0, N1, eval_neg, eval_sub, eval_pow, eval_finsetSum]
  ring

end Poly

section Sigma

variable {F : Type*} [Field F] {k : Type*} [Field k] [DecidableEq k] [Algebra F k]
  (σ : k →ₐ[F] k) (Xs : Finset k) (hXs : Xs.image σ = Xs)
include hXs

theorem sum_comp_eq {M : Type*} [AddCommMonoid M] (g : k → M) :
    ∑ ξ ∈ Xs, g (σ ξ) = ∑ ξ ∈ Xs, g ξ := by
  have hinj : Function.Injective σ := (σ : k →+* k).injective
  conv_rhs => rw [← hXs]
  rw [Finset.sum_image fun a _ b _ h => hinj h]

theorem prod_comp_eq {M : Type*} [CommMonoid M] (g : k → M) :
    ∏ ξ ∈ Xs, g (σ ξ) = ∏ ξ ∈ Xs, g ξ := by
  have hinj : Function.Injective σ := (σ : k →+* k).injective
  conv_rhs => rw [← hXs]
  rw [Finset.prod_image fun a _ b _ h => hinj h]

theorem map_D : (D Xs).map (σ : k →+* k) = D Xs := by
  rw [D, Polynomial.map_prod]
  simp only [Polynomial.map_sub, map_X, map_C, RingHom.coe_coe]
  exact prod_comp_eq σ Xs hXs fun ξ => X - C ξ

theorem map_E (ξ : k) : (E Xs ξ).map (σ : k →+* k) = E Xs (σ ξ) := by
  have hinj : Function.Injective σ := (σ : k →+* k).injective
  rw [E, E, Polynomial.map_prod]
  simp only [Polynomial.map_sub, map_X, map_C, RingHom.coe_coe]
  conv_rhs => rw [← hXs, ← Finset.image_erase hinj, Finset.prod_image fun a _ b _ h => hinj h]

variable (t u A : k → k) (a₁ a₃ : k) (ht : ∀ ξ, σ (t ξ) = t (σ ξ)) (hu : ∀ ξ, σ (u ξ) = u (σ ξ))
  (hA : ∀ ξ, σ (A ξ) = A (σ ξ)) (ha₁ : σ a₁ = a₁) (ha₃ : σ a₃ = a₃)
include ht hu

theorem map_Pk : (Pk Xs t u).map (σ : k →+* k) = Pk Xs t u := by
  simp only [Pk, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sum,
    Polynomial.map_sub, map_X, map_C, RingHom.coe_coe, map_D σ Xs hXs, map_E σ Xs hXs, ht, hu]
  congr 1
  exact sum_comp_eq σ Xs hXs fun ξ => (C (t ξ) * (X - C ξ) + C (u ξ)) * E Xs ξ ^ 2

theorem map_N1 : (N1 Xs t u).map (σ : k →+* k) = N1 Xs t u := by
  simp only [N1, M1, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_sum, Polynomial.map_sub, map_X, map_C, RingHom.coe_coe, map_D σ Xs hXs,
    map_E σ Xs hXs, ht, hu, map_mul σ, map_ofNat σ]
  first
    | rw [← sum_comp_eq σ Xs hXs fun ξ => (C (2 * u ξ) + C (t ξ) * (X - C ξ)) * E Xs ξ ^ 3]
    | rw [sum_comp_eq σ Xs hXs fun ξ => (C (2 * u ξ) + C (t ξ) * (X - C ξ)) * E Xs ξ ^ 3]

include hA ha₁ ha₃ in
theorem map_N0 : (N0 Xs t u A a₁ a₃).map (σ : k →+* k) = N0 Xs t u A a₁ a₃ := by
  simp only [N0, M0, Polynomial.map_neg, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_sum, Polynomial.map_sub, map_X, map_C, RingHom.coe_coe,
    map_E σ Xs hXs, ht, hu, hA, ha₁, ha₃, map_mul σ]
  first
    | rw [← sum_comp_eq σ Xs hXs fun ξ =>
        (C (u ξ) * (C a₁ * X + C a₃) + (C (a₁ * t ξ) * (X - C ξ) + C (A ξ)) * (X - C ξ)) * E Xs ξ ^ 3]
    | rw [sum_comp_eq σ Xs hXs fun ξ =>
        (C (u ξ) * (C a₁ * X + C a₃) + (C (a₁ * t ξ) * (X - C ξ) + C (A ξ)) * (X - C ξ)) * E Xs ξ ^ 3]

end Sigma

section Curve

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k] (W : WeierstrassCurve F)

def tF : F[X] := C 6 * X ^ 2 + C W.b₂ * X + C W.b₄

def AF : F[X] :=
  C (2 * W.a₁) * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) +
    C W.a₁ * (C W.a₁ * X + C W.a₃) ^ 2 + (C 3 * X ^ 2 + C (2 * W.a₂) * X + C W.a₄) * (C W.a₁ * X + C W.a₃)

theorem veluT_bc (ξ η : k) : (W.baseChange k).veluT ξ η = aeval ξ (tF W) := by
  rw [veluT_eq]
  simp [tF, baseChange, b₂, b₄, map_ofNat]

theorem veluU_bc {ξ η : k} (h : (W.baseChange k).toAffine.Equation ξ η) :
    (W.baseChange k).veluU ξ η = aeval ξ W.Ψ₂Sq := by
  rw [veluU_eq_Ψ₂Sq_eval _ h]
  change ((W.map (algebraMap F k)).Ψ₂Sq).eval ξ = _
  rw [map_Ψ₂Sq, eval_map_algebraMap]

theorem veluA_bc {ξ η : k} (h : (W.baseChange k).toAffine.Equation ξ η) :
    -((W.baseChange k).veluT ξ η * η) +
        ((W.baseChange k).a₁ * (W.baseChange k).veluU ξ η -
          (W.baseChange k).veluGx ξ η * (W.baseChange k).veluGy ξ η) = aeval ξ (AF W) := by
  rw [Affine.equation_iff] at h
  simp only [baseChange, toAffine, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at h
  simp [AF, veluT, veluU, veluGx, veluGy, baseChange, map_ofNat]
  linear_combination 2 * algebraMap F k W.a₁ * h

theorem a₁_bc : (W.baseChange k).a₁ = algebraMap F k W.a₁ := rfl

theorem a₃_bc : (W.baseChange k).a₃ = algebraMap F k W.a₃ := rfl

end Curve

section Main

variable {F : Type*} [Field F] [Fintype F] (k : Type*) [Field k] [DecidableEq k] [Algebra F k]
  (W : WeierstrassCurve F) [W.IsElliptic]

scoped instance instIsEllipticBaseChange : (W.baseChange k).IsElliptic :=
  inferInstanceAs ((W.map (algebraMap F k)).IsElliptic)

omit [Fintype F] in

theorem mem_image_fst_iff {W' : WeierstrassCurve k} {n : ℕ} (Q : W'.toAffine.Point)
    (hQ : addOrderOf Q = 2 * n + 1) (ξ : k) :
    ξ ∈ (W'.oddOrderSummingSet Q n).image Prod.fst ↔
      ∃ η h, (.some ξ η h : W'.toAffine.Point) ∈ AddSubgroup.zmultiples Q := by
  constructor
  · intro hξ
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hξ
    obtain ⟨j, hj1, hjn, hjP⟩ := (W'.mem_oddOrderSummingSet).mp hP
    have hjQ : j • Q ≠ 0 := nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)
    rcases hj : j • Q with _ | ⟨x, y, h⟩
    · exact absurd hj hjQ
    · rw [hj, Affine.Point.coordsOrZero_some] at hjP
      subst hjP
      exact ⟨y, h, hj ▸ ⟨(j : ℤ), natCast_zsmul Q j⟩⟩
  · rintro ⟨η, h, hmem⟩
    have hfin : IsOfFinAddOrder Q := addOrderOf_pos_iff.mp (by rw [hQ]; omega)
    rw [hfin.mem_zmultiples_iff_mem_range_addOrderOf, Finset.mem_image] at hmem
    obtain ⟨j, hj, hjP⟩ := hmem
    rw [Finset.mem_range, hQ] at hj
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [zero_nsmul] at hjP
      exact Affine.Point.some_ne_zero h hjP.symm
    by_cases hjn : j ≤ n
    · refine Finset.mem_image.mpr ⟨(ξ, η), (W'.mem_oddOrderSummingSet).mpr ⟨j, by omega, hjn, ?_⟩, rfl⟩
      simp only [hjP, Affine.Point.coordsOrZero_some]
    · refine Finset.mem_image.mpr ⟨(ξ, W'.toAffine.negY ξ η),
        (W'.mem_oddOrderSummingSet).mpr ⟨2 * n + 1 - j, by omega, by omega, ?_⟩, rfl⟩
      have hneg : (2 * n + 1 - j) • Q = -(j • Q) := by
        rw [eq_neg_iff_add_eq_zero, ← add_nsmul, Nat.sub_add_cancel (by omega), ← hQ,
          addOrderOf_nsmul_eq_zero]
      simp only [hneg, hjP, Affine.Point.neg_some, Affine.Point.coordsOrZero_some]

theorem main (σ : k →ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓF : (ℓ : F) ≠ 0)
    (Q : (W.baseChange k).toAffine.Point) (hQ : addOrderOf Q = ℓ)
    (hσQ : Affine.Point.map (W' := W) σ Q ∈ AddSubgroup.zmultiples Q) :
    ∃ V : WeierstrassCurve F, V.IsElliptic ∧
      ∃ φ : (W.baseChange k).toAffine.Point →+ (V.baseChange k).toAffine.Point,
        φ.ker = AddSubgroup.zmultiples Q ∧
        ∃ (P S N₀ N₁ R : F[X]) (B : Set k), P.Monic ∧ P.natDegree = S.natDegree + 1 ∧
          IsCoprime P S ∧ B.Finite ∧
          ∀ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y), x ∉ B →
            aeval x S ≠ 0 ∧ aeval x R ≠ 0 ∧
            ∃ h', φ (.some x y h) =
              .some (aeval x P / aeval x S) ((aeval x N₀ + aeval x N₁ * y) / aeval x R) h' := by

  have hodd : ℓ % 2 = 1 := hℓ.eq_two_or_odd.resolve_left hℓ2
  have hQ' : addOrderOf Q = 2 * (ℓ / 2) + 1 := by rw [hQ]; omega
  have hℓk : (ℓ : k) ≠ 0 := by
    rw [← map_natCast (algebraMap F k)]
    exact (_root_.map_ne_zero _).mpr hℓF

  have hVelu := (W.baseChange k).exists_veluPointHom_oddOrderSummingSet hℓ hℓ2 hℓk Q hQ
  set S₀ : Finset (k × k) := (W.baseChange k).oddOrderSummingSet Q (ℓ / 2) with hS₀
  obtain ⟨φ₀, hker, hφ₀⟩ := hVelu
  have hOdd : (W.baseChange k).IsOddVeluSet S₀ :=
    isOddVeluSet_oddOrderSummingSet hℓ hℓ2 hQ (by omega)
  set Xs : Finset k := S₀.image Prod.fst with hXsdef
  have hmemXs : ∀ ξ, ξ ∈ Xs ↔ ∃ η h,
      (.some ξ η h : (W.baseChange k).toAffine.Point) ∈ AddSubgroup.zmultiples Q :=
    mem_image_fst_iff k Q hQ'

  have hinj : Function.Injective σ := (σ : k →+* k).injective
  have hXs : Xs.image σ = Xs := by
    refine Finset.eq_of_subset_of_card_le (fun ξ' hξ' => ?_)
      (Finset.card_image_of_injective Xs hinj).ge
    obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.mp hξ'
    obtain ⟨η, h, hmem⟩ := (hmemXs ξ).mp hξ
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    have hmap : Affine.Point.map (W' := W) σ (.some ξ η h) ∈ AddSubgroup.zmultiples Q := by
      rw [← hm, map_zsmul]
      exact AddSubgroup.zsmul_mem _ hσQ m
    rw [Affine.Point.map_some] at hmap
    exact (hmemXs (σ ξ)).mpr ⟨_, _, hmap⟩

  obtain ⟨t, ht⟩ : ∃ t : k → k, ∀ ξ, t ξ = aeval ξ (tF W) := ⟨_, fun _ => rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : k → k, ∀ ξ, u ξ = aeval ξ W.Ψ₂Sq := ⟨_, fun _ => rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : k → k, ∀ ξ, A ξ = aeval ξ (AF W) := ⟨_, fun _ => rfl⟩
  have hσt : ∀ ξ, σ (t ξ) = t (σ ξ) := fun ξ => by
    rw [ht, ht]; exact (aeval_algHom_apply σ ξ (tF W)).symm
  have hσu : ∀ ξ, σ (u ξ) = u (σ ξ) := fun ξ => by
    rw [hu, hu]; exact (aeval_algHom_apply σ ξ W.Ψ₂Sq).symm
  have hσA : ∀ ξ, σ (A ξ) = A (σ ξ) := fun ξ => by
    rw [hA, hA]; exact (aeval_algHom_apply σ ξ (AF W)).symm
  have ha₁ : σ (W.baseChange k).a₁ = (W.baseChange k).a₁ := σ.commutes W.a₁
  have ha₃ : σ (W.baseChange k).a₃ = (W.baseChange k).a₃ := σ.commutes W.a₃

  have hveluX : ∀ x, x ∉ Xs → (W.baseChange k).veluX S₀ x =
      (Pk Xs t u).eval x / (D Xs).eval x ^ 2 := by
    intro x hx
    rw [eval_Pk_div Xs t u hx, veluX, hXsdef,
      Finset.sum_image fun P hP P' hP' h => hOdd.x_injOn P hP P' hP' h]
    refine congr_arg _ (Finset.sum_congr rfl fun P hP => ?_)
    rw [veluT_bc, veluU_bc W (hOdd.equation P hP), ht, hu]
  have hveluY : ∀ x y, x ∉ Xs → (W.baseChange k).veluY S₀ x y =
      ((N0 Xs t u A (W.baseChange k).a₁ (W.baseChange k).a₃).eval x + (N1 Xs t u).eval x * y) /
        (D Xs).eval x ^ 3 := by
    intro x y hx
    rw [eval_N_div Xs t u A _ _ hx, veluY, hXsdef,
      Finset.sum_image fun P hP P' hP' h => hOdd.x_injOn P hP P' hP' h]
    refine congr_arg _ (Finset.sum_congr rfl fun P hP => ?_)
    rw [hA, ← veluA_bc W (hOdd.equation P hP), veluT_bc, veluU_bc W (hOdd.equation P hP), ht,
      hu]
    ring

  obtain ⟨P, hPmap, hPdeg, hPmon⟩ := lifts_and_natDegree_eq_and_monic
    (lifts_of_map_eq σ hσ (map_Pk σ Xs hXs t u hσt hσu)) (monic_Pk Xs t u)
  obtain ⟨S, hSmap⟩ := (mem_lifts _).mp (lifts_of_map_eq σ hσ (p := D Xs ^ 2)
    (by rw [Polynomial.map_pow, map_D σ Xs hXs]))
  obtain ⟨R, hRmap⟩ := (mem_lifts _).mp (lifts_of_map_eq σ hσ (p := D Xs ^ 3)
    (by rw [Polynomial.map_pow, map_D σ Xs hXs]))
  obtain ⟨N₁, hN₁map⟩ := (mem_lifts _).mp (lifts_of_map_eq σ hσ (map_N1 σ Xs hXs t u hσt hσu))
  obtain ⟨N₀, hN₀map⟩ := (mem_lifts _).mp
    (lifts_of_map_eq σ hσ (map_N0 σ Xs hXs t u A _ _ hσt hσu hσA ha₁ ha₃))

  have hTsum : (W.baseChange k).veluTSum S₀ = ∑ ξ ∈ Xs, t ξ := by
    rw [veluTSum, hXsdef, Finset.sum_image fun P hP P' hP' h => hOdd.x_injOn P hP P' hP' h]
    exact Finset.sum_congr rfl fun P _ => by rw [veluT_bc, ht]
  have hWsum : (W.baseChange k).veluWSum S₀ = ∑ ξ ∈ Xs, (u ξ + ξ * t ξ) := by
    rw [veluWSum, hXsdef, Finset.sum_image fun P hP P' hP' h => hOdd.x_injOn P hP P' hP' h]
    exact Finset.sum_congr rfl fun P hP => by
      rw [veluW, veluT_bc, veluU_bc W (hOdd.equation P hP), ht, hu]
  have hσT : σ ((W.baseChange k).veluTSum S₀) = (W.baseChange k).veluTSum S₀ := by
    rw [hTsum, map_sum]
    simp only [hσt]
    exact sum_comp_eq σ Xs hXs t
  have hσW : σ ((W.baseChange k).veluWSum S₀) = (W.baseChange k).veluWSum S₀ := by
    rw [hWsum, map_sum]
    simp only [map_add, map_mul, hσt, hσu]
    exact sum_comp_eq σ Xs hXs fun ξ => u ξ + ξ * t ξ
  obtain ⟨t₀, ht₀⟩ := mem_range_of_fixed σ hσ hσT
  obtain ⟨w₀, hw₀⟩ := mem_range_of_fixed σ hσ hσW
  let V : WeierstrassCurve F := ⟨W.a₁, W.a₂, W.a₃, W.a₄ - 5 * t₀, W.a₆ - W.b₂ * t₀ - 7 * w₀⟩
  have hVk : V.baseChange k = (W.baseChange k).veluQuotient S₀ := by
    ext
    · rfl
    · rfl
    · rfl
    · change algebraMap F k (W.a₄ - 5 * t₀) = (W.baseChange k).a₄ - 5 * _
      rw [← ht₀, map_sub, map_mul, map_ofNat]; rfl
    · change algebraMap F k (W.a₆ - W.b₂ * t₀ - 7 * w₀) = (W.baseChange k).a₆ - _ * _ - 7 * _
      rw [← ht₀, ← hw₀, map_sub, map_sub, map_mul, map_mul, map_ofNat, ← map_b₂]; rfl
  have hVΔ : (V.baseChange k).Δ ≠ 0 := by
    rw [hVk]
    exact (W.baseChange k).veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq
      (ℓ / 2) Q hQ'
  have hVell : V.IsElliptic := by
    rw [isElliptic_iff]
    refine Ne.isUnit fun h0 => hVΔ ?_
    change (V.map (algebraMap F k)).Δ = 0
    rw [map_Δ, h0, map_zero]

  refine ⟨V, hVell, ?_⟩
  rw [hVk]
  refine ⟨φ₀, hker, P, S, N₀, N₁, R, ↑Xs, hPmon, ?_, ?_, Xs.finite_toSet, ?_⟩
  · rw [hPdeg, natDegree_Pk, ← hSmap, natDegree_map_eq_of_injective (algebraMap F k).injective]
  · rw [← isCoprime_map (algebraMap F k), hPmap, hSmap]
    refine isCoprime_Pk Xs t u fun ξ hξ => ?_
    obtain ⟨P₀, hP₀, rfl⟩ := Finset.mem_image.mp hξ
    rw [hu, ← veluU_bc W (hOdd.equation P₀ hP₀), veluU]
    exact pow_ne_zero _ (hOdd.gy_ne_zero P₀ hP₀)
  · intro x y h hx
    rw [Finset.mem_coe] at hx
    have hD := eval_D_ne_zero Xs hx
    have hS : aeval x S = (D Xs).eval x ^ 2 := by
      rw [← eval_map_algebraMap, hSmap, eval_pow]
    have hR : aeval x R = (D Xs).eval x ^ 3 := by
      rw [← eval_map_algebraMap, hRmap, eval_pow]
    refine ⟨by rw [hS]; exact pow_ne_zero _ hD, by rw [hR]; exact pow_ne_zero _ hD, ?_⟩
    have hnot : (.some x y h : (W.baseChange k).toAffine.Point) ∉ AddSubgroup.zmultiples Q :=
      fun hmem => hx ((hmemXs x).mpr ⟨y, h, hmem⟩)
    obtain ⟨h', e⟩ := hφ₀ x y h hnot
    have ex : (W.baseChange k).veluX S₀ x = aeval x P / aeval x S := by
      rw [hveluX x hx, hS, ← eval_map_algebraMap, hPmap]
    have ey : (W.baseChange k).veluY S₀ x y =
        (aeval x N₀ + aeval x N₁ * y) / aeval x R := by
      rw [hveluY x y hx, hR, ← eval_map_algebraMap, hN₀map, ← eval_map_algebraMap, hN₁map]
    have key : ∀ {x' y' : k}, x' = (W.baseChange k).veluX S₀ x →
        y' = (W.baseChange k).veluY S₀ x y →
          ∃ h'', φ₀ (.some x y h) = .some x' y' h'' := by
      rintro _ _ rfl rfl
      exact ⟨h', e⟩
    exact key ex.symm ey.symm

end Main

end WeierstrassCurve.FrobVeluDescent
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_rational_separable_isogeny_of_map_mem_zmultiples.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_rational_separable_isogeny_of_map_mem_zmultiples.WeierstrassCurve.FrobVeluDescent"
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_rational_separable_isogeny_of_map_mem_zmultiples.WeierstrassCurve"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_rational_separable_isogeny_of_map_mem_zmultiples.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_rational_separable_isogeny_of_map_mem_zmultiples.WeierstrassCurve.FrobVeluDescent"

theorem solution
    {F : Type*} [Field F] [Fintype F] (k : Type*) [Field k] [DecidableEq k] [Algebra F k]
    (W : WeierstrassCurve F) [W.IsElliptic]
    (σ : k →ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓF : (ℓ : F) ≠ 0)
    (Q : (W.baseChange k).toAffine.Point) (hQ : addOrderOf Q = ℓ)
    (hσQ : WeierstrassCurve.Affine.Point.map (W' := W) σ Q ∈ AddSubgroup.zmultiples Q) :
    ∃ V : WeierstrassCurve F, V.IsElliptic ∧
      ∃ φ : (W.baseChange k).toAffine.Point →+ (V.baseChange k).toAffine.Point,
        φ.ker = AddSubgroup.zmultiples Q ∧
        ∃ (P S N₀ N₁ R : F[X]) (B : Set k), P.Monic ∧ P.natDegree = S.natDegree + 1 ∧
          IsCoprime P S ∧ B.Finite ∧
          ∀ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y), x ∉ B →
            aeval x S ≠ 0 ∧ aeval x R ≠ 0 ∧
            ∃ h', φ (.some x y h) =
              .some (aeval x P / aeval x S) ((aeval x N₀ + aeval x N₁ * y) / aeval x R) h' :=
  WeierstrassCurve.FrobVeluDescent.main k W σ hσ hℓ hℓ2 hℓF Q hQ hσQ

end S_WeierstrassCurve_exists_rational_separable_isogeny_of_map_mem_zmultiples
end P2MW
export P2MW.S_WeierstrassCurve_exists_rational_separable_isogeny_of_map_mem_zmultiples (solution)
