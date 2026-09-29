-- Prove2me | solution 1 for WeierstrassCurve.free_and_finrank_rationalEndSubring_eq_four
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/8889bf4e-d47b-5e02-aebf-7708b1a6dedf

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_DualIsogenyAPI
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_dualIsogenyExistence_rationalEndSubring
import Theorems.Thm_WeierstrassCurve_exists_iterate_frobenius_eq_smul_of_forall_nsmul_char_eq_zero
import Theorems.Thm_WeierstrassCurve_exists_anticommuting_pair_mem_rationalHomSet_of_frobenius_eq_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_free_and_finrank_rationalEndSubring_eq_four
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_free_and_finrank_rationalEndSubring_eq_four.WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point Polynomial"
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY a₃ map_map a₁ map a₄ a₂ a₆ toAffine Affine.Point map_Δ Δ Affine.Point.neg_some baseChange j evalEvalBC IsRationallyRepresented rationalHomSet rationalEndSubring zero_mem_rationalHomSet id_mem_rationalHomSet add_mem_rationalHomSet comp_mem_rationalHomSet surjective_of_mem_rationalHomSet card_torsion_of_isAlgClosed dualIsogenyExistence_rationalEndSubring exists_iterate_frobenius_eq_smul_of_forall_nsmul_char_eq_zero exists_anticommuting_pair_mem_rationalHomSet_of_frobenius_eq_smul"
namespace SupersingularEndRank
p2m_open "WeierstrassCurve"

section IntArith

theorem dvd_of_root {x m a b : ℤ} (hm : m ≠ 0) (h : x * x - m * a * x + m * m * b = 0) : m ∣ x := by
  obtain ⟨g, x', m', hg, hcop, hx, hm'⟩ :=
    Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_right x hm)
  have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  have h' : x' * x' - m' * a * x' + m' * m' * b = 0 := by
    have : (g : ℤ) * g * (x' * x' - m' * a * x' + m' * m' * b) = 0 := by
      rw [hx, hm'] at h; linear_combination h
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd (mul_self_eq_zero.mp h0) hg0
    · exact h0
  have hcop' : IsCoprime m' x' := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]; exact hcop
  have hdvd : m' ∣ x' * x' := ⟨a * x' - m' * b, by linear_combination h'⟩
  have hunit : IsUnit m' :=
    hcop'.isUnit_of_dvd' (dvd_refl _) (hcop'.dvd_of_dvd_mul_left hdvd)
  rcases Int.isUnit_iff.mp hunit with h1 | h1
  · exact ⟨x', by rw [hx, hm', h1]; ring⟩
  · exact ⟨-x', by rw [hx, hm', h1]; ring⟩

theorem msq_ne_zero {t l : ℤ} (hd : ∀ s : ℤ, t * t - 4 * l ≠ s * s) (u : ℤ) :
    u * u - 2 * t * u + 4 * l ≠ 0 := fun h =>
  hd (u - t) (by linear_combination -h)

end IntArith

section CommAlg

variable {C : Type*} [CommRing C] {π : C} {t l : ℤ}

theorem exists_mul_eq (hπ : π * π - t * π + l = 0) {α : C} {a b a' b' : ℤ}
    (hα : α * α - a * α + b = 0) (hα' : (α + π) * (α + π) - a' * (α + π) + b' = 0) :
    ∃ x y : ℤ, (((a' - a) * (a' - a) - 2 * t * (a' - a) + 4 * l : ℤ) : C) * α = x + y * π := by
  refine ⟨(2 * t - (a' - a)) * (b + l - b') + 2 * l * (a' - t),
    -(a' - a) * (a' - t) - 2 * (b + l - b'), ?_⟩
  push_cast
  linear_combination (2 * t - (a' - a) - 2 * π) * hα' - (2 * t - (a' - a) - 2 * π) * hα
    + (4 * α - 2 * (a' - t) - (2 * t - (a' - a) - 2 * π)) * hπ

end CommAlg

section QuadRing

variable {R : Type*} [Ring R]

structure QH (R : Type*) [Ring R] : Prop where
  tf : ∀ (n : ℤ) (c : R), n ≠ 0 → n • c = 0 → c = 0
  ci : ∀ n : ℤ, (n : R) = 0 → n = 0
  nzd : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0
  quad : ∀ r : R, ∃ t n : ℤ, r * r = t • r - n • (1 : R)

def IsScal (r : R) : Prop := ∃ m : ℤ, (m : R) = r

namespace QH

variable (H : QH R)
include H

theorem ci' {n : ℤ} (h : n • (1 : R) = 0) : n = 0 := H.ci n (by rwa [zsmul_one] at h)

theorem smul_one_inj {a b : ℤ} (h : a • (1 : R) = b • (1 : R)) : a = b := by
  have := H.ci' (n := a - b) (by rw [sub_smul, h, sub_self])
  omega

theorem cast_inj {a b : ℤ} (h : (a : R) = b) : a = b :=
  H.smul_one_inj (by rwa [zsmul_one, zsmul_one])

theorem isScal_of_smul_eq {r : R} {c m : ℤ} (hc : c ≠ 0) (h : c • r = (m : R)) : IsScal r := by
  obtain ⟨t, n, hr⟩ := H.quad r
  have h1 : c • r = m • (1 : R) := by rw [h, zsmul_one]
  have key : (m * m) • (1 : R) = (c * t * m - c * c * n) • (1 : R) := by
    calc (m * m) • (1 : R) = (m • (1 : R)) * (m • (1 : R)) := by
            simp only [mul_smul_comm, mul_one, smul_smul]
      _ = (c • r) * (c • r) := by rw [h1]
      _ = (c * c) • (t • r - n • (1 : R)) := by
            rw [← hr]; simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
      _ = (c * t) • (c • r) - (c * c * n) • (1 : R) := by simp only [smul_sub, smul_smul]; module
      _ = (c * t) • (m • (1 : R)) - (c * c * n) • (1 : R) := by rw [h1]
      _ = (c * t * m - c * c * n) • (1 : R) := by simp only [smul_smul]; module
  have hint : m * m - c * t * m + c * c * n = 0 := by
    have := H.smul_one_inj key
    linarith
  obtain ⟨e, rfl⟩ := dvd_of_root hc hint
  refine ⟨e, ?_⟩
  have h2 : c • (r - (e : R)) = 0 := by
    rw [smul_sub, h1, ← zsmul_one e, smul_smul, sub_self]
  exact (sub_eq_zero.mp (H.tf c _ hc h2)).symm

theorem eq_of_not_isScal {r : R} (hr : ¬ IsScal r) {t n t' n' : ℤ}
    (h : r * r = t • r - n • (1 : R)) (h' : r * r = t' • r - n' • (1 : R)) : t = t' ∧ n = n' := by
  have e : (t - t') • r = ((n - n' : ℤ) : R) := by
    rw [← zsmul_one]
    have hh := h.symm.trans h'
    calc (t - t') • r = (t • r - n • (1 : R)) - (t' • r - n' • (1 : R)) + (n - n') • (1 : R) := by
            module
      _ = (n - n') • (1 : R) := by rw [hh, sub_self, zero_add]
  by_cases htt : t - t' = 0
  · have ht : t = t' := by omega
    refine ⟨ht, ?_⟩
    rw [htt, zero_smul] at e
    have := H.ci _ e.symm
    omega
  · exact absurd (H.isScal_of_smul_eq htt e) hr

noncomputable def tr (r : R) : ℤ := by
  classical
  exact if h : IsScal r then 2 * h.choose else (H.quad r).choose

noncomputable def nm (r : R) : ℤ := by
  classical
  exact if h : IsScal r then h.choose * h.choose else (H.quad r).choose_spec.choose

theorem sq_eq (r : R) : r * r = H.tr r • r - H.nm r • (1 : R) := by
  classical
  unfold tr nm
  split_ifs with h
  · have hm := h.choose_spec
    generalize h.choose = m at hm ⊢
    rw [← hm, ← zsmul_one]
    simp only [mul_smul_comm, mul_one, smul_smul]
    module
  · exact (H.quad r).choose_spec.choose_spec

theorem tr_intCast (m : ℤ) : H.tr (m : R) = 2 * m := by
  classical
  have h : IsScal (m : R) := ⟨m, rfl⟩
  unfold tr
  rw [dif_pos h, H.cast_inj h.choose_spec]

theorem nm_intCast (m : ℤ) : H.nm (m : R) = m * m := by
  classical
  have h : IsScal (m : R) := ⟨m, rfl⟩
  unfold nm
  rw [dif_pos h, H.cast_inj h.choose_spec]

theorem tr_eq {r : R} {t n : ℤ} (h : r * r = t • r - n • (1 : R))
    (hs : ∀ m : ℤ, (m : R) = r → t = 2 * m) : H.tr r = t := by
  by_cases hsc : IsScal r
  · obtain ⟨m, hm⟩ := hsc
    rw [← hm, tr_intCast]
    exact (hs m hm).symm
  · exact (H.eq_of_not_isScal hsc (H.sq_eq r) h).1

theorem nm_eq {r : R} {t n : ℤ} (h : r * r = t • r - n • (1 : R))
    (hs : ∀ m : ℤ, (m : R) = r → n = m * m) : H.nm r = n := by
  by_cases hsc : IsScal r
  · obtain ⟨m, hm⟩ := hsc
    rw [← hm, nm_intCast]
    exact (hs m hm).symm
  · exact (H.eq_of_not_isScal hsc (H.sq_eq r) h).2

theorem tr_zero : H.tr 0 = 0 := by
  have := H.tr_intCast 0
  rwa [Int.cast_zero, mul_zero] at this

theorem nm_zero : H.nm 0 = 0 := by
  have := H.nm_intCast 0
  rwa [Int.cast_zero, mul_zero] at this

theorem disc_ne_sq {x : R} (hx : ¬ IsScal x) (s : ℤ) : H.tr x * H.tr x - 4 * H.nm x ≠ s * s := by
  intro hs
  have hq := H.sq_eq x
  have key : ((2 : ℤ) • x - (H.tr x + s) • (1 : R)) * ((2 : ℤ) • x - (H.tr x - s) • (1 : R)) = 0 := by
    have e : ((2 : ℤ) • x - (H.tr x + s) • (1 : R)) * ((2 : ℤ) • x - (H.tr x - s) • (1 : R))
        = (4 : ℤ) • (x * x) - (4 * H.tr x) • x + (H.tr x * H.tr x - s * s) • (1 : R) := by
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, smul_sub,
        smul_smul]
      module
    rw [e, hq, ← hs]
    simp only [smul_sub, smul_smul]
    module
  rcases H.nzd _ _ key with h0 | h0
  · exact hx (H.isScal_of_smul_eq (c := 2) (m := H.tr x + s) two_ne_zero
      (by rw [← zsmul_one]; exact sub_eq_zero.mp h0))
  · exact hx (H.isScal_of_smul_eq (c := 2) (m := H.tr x - s) two_ne_zero
      (by rw [← zsmul_one]; exact sub_eq_zero.mp h0))

theorem tr_intCast_add (m : ℤ) (y : R) : H.tr ((m : R) + y) = 2 * m + H.tr y := by
  by_cases hy : IsScal y
  · obtain ⟨m', rfl⟩ := hy
    rw [← Int.cast_add, tr_intCast, tr_intCast]; ring
  · have hq := H.sq_eq y
    apply H.tr_eq (n := m * m + H.tr y * m + H.nm y)
    · rw [← zsmul_one m]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, hq, smul_add,
        smul_smul]
      module
    · intro m' hm'
      exact absurd ⟨m' - m, by rw [Int.cast_sub, hm', add_sub_cancel_left]⟩ hy

theorem tr_formula {x z : R} (hx : ¬ IsScal x) {D A B : ℤ} (hD : D ≠ 0)
    (hz : D • z = A • (1 : R) + B • x) : D * H.tr z = 2 * A + B * H.tr x := by
  have hqz := H.sq_eq z
  have hqx := H.sq_eq x

  have e1 : (D • z) * (D • z) = (D * H.tr z * A - D * D * H.nm z) • (1 : R) + (D * H.tr z * B) • x := by
    calc (D • z) * (D • z) = (D * D) • (z * z) := by
            simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
      _ = (D * H.tr z) • (D • z) - (D * D * H.nm z) • (1 : R) := by
            rw [hqz]; simp only [smul_sub, smul_smul]; module
      _ = _ := by rw [hz]; simp only [smul_add, smul_smul]; module
  have e2 : (D • z) * (D • z) = (A * A - B * B * H.nm x) • (1 : R) + (2 * A * B + B * B * H.tr x) • x := by
    rw [hz]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, smul_add, smul_smul,
      hqx, smul_sub]
    module
  have e3 : (D * H.tr z * B - 2 * A * B - B * B * H.tr x) • x
      = (((A * A - B * B * H.nm x) - (D * H.tr z * A - D * D * H.nm z) : ℤ) : R) := by
    rw [← zsmul_one]
    have hh := e1.symm.trans e2
    calc (D * H.tr z * B - 2 * A * B - B * B * H.tr x) • x
        = ((D * H.tr z * A - D * D * H.nm z) • (1 : R) + (D * H.tr z * B) • x)
          - ((A * A - B * B * H.nm x) • (1 : R) + (2 * A * B + B * B * H.tr x) • x)
          + ((A * A - B * B * H.nm x) - (D * H.tr z * A - D * D * H.nm z)) • (1 : R) := by module
      _ = _ := by rw [hh, sub_self, zero_add]
  have hc : D * H.tr z * B - 2 * A * B - B * B * H.tr x = 0 := by
    by_contra hne
    exact hx (H.isScal_of_smul_eq hne e3)
  by_cases hB : B = 0
  · subst hB
    rw [zero_smul, add_zero, zsmul_one] at hz
    obtain ⟨e, rfl⟩ := H.isScal_of_smul_eq hD hz
    rw [← zsmul_one e, smul_smul, zsmul_one] at hz
    have := H.cast_inj hz
    rw [tr_intCast, zero_mul, add_zero, ← this]; ring
  · have : B * (D * H.tr z - 2 * A - B * H.tr x) = 0 := by linear_combination hc
    have := (mul_eq_zero.mp this).resolve_left hB
    linarith

open scoped IsMulCommutative in

theorem tr_add_of_commute {x y : R} (hxy : x * y = y * x) (hx : ¬ IsScal x) (hy : ¬ IsScal y) :
    H.tr (x + y) = H.tr x + H.tr y := by
  have hcomm : ∀ a ∈ ({x, y} : Set R), ∀ b ∈ ({x, y} : Set R), a * b = b * a := by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    exacts [rfl, hxy, hxy.symm, rfl]
  haveI := Subring.isMulCommutative_closure hcomm
  set C := Subring.closure ({x, y} : Set R) with hC
  have hxm : x ∈ C := Subring.subset_closure (by simp)
  have hym : y ∈ C := Subring.subset_closure (by simp)
  have hqx := H.sq_eq x
  have hqy := H.sq_eq y
  have hqs := H.sq_eq (y + x)

  have hπ : (⟨x, hxm⟩ : C) * ⟨x, hxm⟩ - (H.tr x : C) * ⟨x, hxm⟩ + (H.nm x : C) = 0 := by
    apply Subtype.ext
    push_cast
    rw [hqx, ← zsmul_eq_mul, ← zsmul_one (H.nm x)]; module
  have hα : (⟨y, hym⟩ : C) * ⟨y, hym⟩ - (H.tr y : C) * ⟨y, hym⟩ + (H.nm y : C) = 0 := by
    apply Subtype.ext
    push_cast
    rw [hqy, ← zsmul_eq_mul, ← zsmul_one (H.nm y)]; module
  have hα' : ((⟨y, hym⟩ : C) + ⟨x, hxm⟩) * (⟨y, hym⟩ + ⟨x, hxm⟩)
      - (H.tr (y + x) : C) * (⟨y, hym⟩ + ⟨x, hxm⟩) + (H.nm (y + x) : C) = 0 := by
    apply Subtype.ext
    push_cast
    rw [hqs, ← zsmul_eq_mul, ← zsmul_one (H.nm (y + x))]; module
  obtain ⟨X₀, Y₀, hXY⟩ := exists_mul_eq hπ hα hα'
  set M : ℤ := (H.tr (y + x) - H.tr y) * (H.tr (y + x) - H.tr y) - 2 * H.tr x * (H.tr (y + x) - H.tr y)
    + 4 * H.nm x with hM
  have hM0 : M ≠ 0 := msq_ne_zero (H.disc_ne_sq hx) _
  have hR : M • y = X₀ • (1 : R) + Y₀ • x := by
    have h := congrArg Subtype.val hXY
    simp only [Subring.coe_mul, SubringClass.coe_intCast, Subring.coe_add] at h
    rw [zsmul_eq_mul, zsmul_eq_mul, zsmul_eq_mul, mul_one]
    exact h
  have hR' : M • (x + y) = X₀ • (1 : R) + (Y₀ + M) • x := by
    rw [smul_add, hR]; module
  have f1 := H.tr_formula hx hM0 hR
  have f2 := H.tr_formula hx hM0 hR'
  have : M * (H.tr (x + y) - H.tr x - H.tr y) = 0 := by linear_combination f2 - f1
  have := (mul_eq_zero.mp this).resolve_left hM0
  linarith

theorem tr_add_of_not_commute {x y : R} (hxy : x * y ≠ y * x) :
    H.tr (x + y) = H.tr x + H.tr y := by
  have hx := H.sq_eq x
  have hy := H.sq_eq y
  have hs := H.sq_eq (x + y)
  have key : (H.tr (x + y) - H.tr x - H.tr y) • (x * y - y * x) = 0 := by
    have e1 : x * ((x + y) * (x + y)) - ((x + y) * (x + y)) * x = H.tr (x + y) • (x * y - y * x) := by
      rw [hs]
      simp only [sub_mul, mul_sub, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
        smul_sub, smul_add]
      module
    have e2 : x * ((x + y) * (x + y)) - ((x + y) * (x + y)) * x
        = (x * x) * y - y * (x * x) + (x * (y * y) - (y * y) * x) := by noncomm_ring
    rw [hx, hy] at e2
    rw [e2] at e1
    rw [sub_smul, sub_smul, ← e1]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
      smul_sub]
    module
  by_contra hne
  have hne' : H.tr (x + y) - H.tr x - H.tr y ≠ 0 := fun h => hne (by linarith)
  exact hxy (sub_eq_zero.mp (H.tf _ _ hne' key))

theorem tr_add (x y : R) : H.tr (x + y) = H.tr x + H.tr y := by
  by_cases hc : x * y = y * x
  · by_cases hx : IsScal x
    · obtain ⟨m, rfl⟩ := hx
      rw [tr_intCast_add, tr_intCast]
    by_cases hy : IsScal y
    · obtain ⟨m, rfl⟩ := hy
      rw [add_comm, tr_intCast_add, tr_intCast]; ring
    exact H.tr_add_of_commute hc hx hy
  · exact H.tr_add_of_not_commute hc

noncomputable def bar (r : R) : R := H.tr r • (1 : R) - r

theorem bar_add (x y : R) : H.bar (x + y) = H.bar x + H.bar y := by
  unfold bar; rw [tr_add]; module

theorem mul_bar (x : R) : x * H.bar x = H.nm x • (1 : R) := by
  unfold bar
  rw [mul_sub, H.sq_eq x]
  simp only [mul_smul_comm, mul_one]
  module

theorem bar_one : H.bar 1 = 1 := by
  unfold bar
  have := H.tr_intCast 1
  rw [Int.cast_one] at this
  rw [this]; module

theorem bar_of_tr_eq_zero {x : R} (h : H.tr x = 0) : H.bar x = -x := by
  unfold bar; rw [h, zero_smul, zero_sub]

noncomputable def B (x y : R) : ℤ := H.nm (x + y) - H.nm x - H.nm y

theorem B_comm (x y : R) : H.B x y = H.B y x := by
  unfold B; rw [add_comm]; ring

theorem B_spec (x y : R) : H.B x y • (1 : R) = x * H.bar y + y * H.bar x := by
  have hs := H.sq_eq (x + y)
  rw [H.tr_add] at hs
  have hx := H.sq_eq x
  have hy := H.sq_eq y
  have e : x * y + y * x = (x + y) * (x + y) - x * x - y * y := by noncomm_ring
  rw [hs, hx, hy] at e
  have e' : x * H.bar y + y * H.bar x = H.tr y • x + H.tr x • y - (x * y + y * x) := by
    unfold bar
    simp only [mul_sub, mul_smul_comm, mul_one]
    module
  rw [e', e]
  unfold B
  simp only [smul_add, sub_smul]
  module

theorem B_add_left (x₁ x₂ y : R) : H.B (x₁ + x₂) y = H.B x₁ y + H.B x₂ y := by
  apply H.smul_one_inj
  rw [add_smul, B_spec, B_spec, B_spec, bar_add]
  noncomm_ring

theorem B_one_right (x : R) : H.B x 1 = H.tr x := by
  apply H.smul_one_inj
  rw [B_spec, bar_one]
  unfold bar
  noncomm_ring

theorem B_self (x : R) : H.B x x = 2 * H.nm x := by
  apply H.smul_one_inj
  rw [B_spec, mul_bar, mul_smul, two_smul]

theorem B_eq_zero_of_anticomm {a b : R} (ha : H.tr a = 0) (hb : H.tr b = 0)
    (h : a * b = -(b * a)) : H.B a b = 0 := by
  apply H.ci'
  rw [B_spec, H.bar_of_tr_eq_zero ha, H.bar_of_tr_eq_zero hb, mul_neg, mul_neg, h]
  abel

theorem anticomm_of_B_eq_zero {a b : R} (ha : H.tr a = 0) (hb : H.tr b = 0) (h : H.B a b = 0) :
    a * b = -(b * a) := by
  have := H.B_spec a b
  rw [h, zero_smul, H.bar_of_tr_eq_zero ha, H.bar_of_tr_eq_zero hb, mul_neg, mul_neg] at this
  rw [← sub_eq_zero, sub_neg_eq_add, ← neg_eq_zero, neg_add, this]

theorem not_isScal_of_anticomm {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) (h : a * b = -(b * a)) :
    ¬ IsScal a := by
  rintro ⟨m, rfl⟩
  have hc : (m : R) * b = b * m := (Int.cast_commute m b).eq
  rw [hc, ← sub_eq_zero, sub_neg_eq_add, ← two_smul ℤ] at h
  rcases H.nzd _ _ (H.tf 2 _ two_ne_zero h) with h0 | h0
  · exact hb h0
  · exact ha h0

theorem tr_eq_zero_of_sq {a : R} (ha : ¬ IsScal a) {u : ℤ} (h : a * a = (u : R)) : H.tr a = 0 :=
  H.tr_eq (n := -u) (by rw [zero_smul, zero_sub, neg_smul, neg_neg, zsmul_one]; exact h)
    (fun m hm => absurd ⟨m, hm⟩ ha)

theorem nm_eq_of_sq {a : R} (ha : ¬ IsScal a) {u : ℤ} (h : a * a = (u : R)) : H.nm a = -u :=
  H.nm_eq (t := 0) (by rw [zero_smul, zero_sub, neg_smul, neg_neg, zsmul_one]; exact h)
    (fun m hm => absurd ⟨m, hm⟩ ha)

theorem free_and_finite_and_finrank_eq_four {i j : R} {u v : ℤ} (hu : u ≠ 0) (hv : v ≠ 0)
    (hi : i * i = (u : R)) (hj : j * j = (v : R)) (hij : i * j = -(j * i)) :
    Module.Free ℤ R ∧ Module.Finite ℤ R ∧ Module.finrank ℤ R = 4 := by

  have hi0 : i ≠ 0 := by
    rintro rfl; rw [zero_mul] at hi; exact hu (H.ci u hi.symm)
  have hj0 : j ≠ 0 := by
    rintro rfl; rw [zero_mul] at hj; exact hv (H.ci v hj.symm)
  have hk0 : i * j ≠ 0 := fun h0 => by
    rcases H.nzd _ _ h0 with h | h
    · exact hi0 h
    · exact hj0 h

  have hk : (i * j) * (i * j) = ((-(u * v) : ℤ) : R) := by
    have e : (i * j) * (i * j) = i * (j * i) * j := by noncomm_ring
    rw [e, ← neg_eq_iff_eq_neg.mpr hij]
    have e2 : i * -(i * j) * j = -((i * i) * (j * j)) := by noncomm_ring
    rw [e2, hi, hj, ← Int.cast_mul, Int.cast_neg]
  have hji : j * i = -(i * j) := by rw [hij, neg_neg]
  have hik : i * (i * j) = -((i * j) * i) := by
    rw [mul_assoc i j i, hji, mul_neg, neg_neg]
  have hjk : j * (i * j) = -((i * j) * j) := by
    rw [← mul_assoc, hji, neg_mul]

  have hsi : ¬ IsScal i := H.not_isScal_of_anticomm hi0 hj0 hij
  have hsj : ¬ IsScal j := H.not_isScal_of_anticomm hj0 hi0 hji
  have hsk : ¬ IsScal (i * j) :=
    H.not_isScal_of_anticomm hk0 hi0 (by rw [hik, neg_neg])
  have ti : H.tr i = 0 := H.tr_eq_zero_of_sq hsi hi
  have tj : H.tr j = 0 := H.tr_eq_zero_of_sq hsj hj
  have tk : H.tr (i * j) = 0 := H.tr_eq_zero_of_sq hsk hk
  have ni : H.nm i = -u := H.nm_eq_of_sq hsi hi
  have nj : H.nm j = -v := H.nm_eq_of_sq hsj hj
  have nk : H.nm (i * j) = u * v := by rw [H.nm_eq_of_sq hsk hk]; ring
  have t1 : H.tr 1 = 2 := by have := H.tr_intCast 1; rwa [Int.cast_one, mul_one] at this

  have Bij : H.B i j = 0 := H.B_eq_zero_of_anticomm ti tj hij
  have Bik : H.B i (i * j) = 0 := H.B_eq_zero_of_anticomm ti tk hik
  have Bjk : H.B j (i * j) = 0 := H.B_eq_zero_of_anticomm tj tk hjk

  let e : Fin 4 → R := ![1, i, j, i * j]

  let f₀ : R →+ (Fin 4 → ℤ) :=
    AddMonoidHom.mk' (fun r m => H.B r (e m)) (fun a b => by funext m; exact H.B_add_left a b (e m))
  let f : R →ₗ[ℤ] (Fin 4 → ℤ) := f₀.toIntLinearMap
  have hf_apply : ∀ r m, f r m = H.B r (e m) := fun r m => rfl

  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    have h0 : H.B r 1 = 0 := by simpa [hf_apply, e] using congrFun hr 0
    have h1 : H.B r i = 0 := by simpa [hf_apply, e] using congrFun hr 1
    have h2 : H.B r j = 0 := by simpa [hf_apply, e] using congrFun hr 2
    have h3 : H.B r (i * j) = 0 := by simpa [hf_apply, e] using congrFun hr 3
    rw [B_one_right] at h0
    have a1 := H.anticomm_of_B_eq_zero h0 ti h1
    have a2 := H.anticomm_of_B_eq_zero h0 tj h2
    have a3 := H.anticomm_of_B_eq_zero h0 tk h3

    have a4 : r * (i * j) = (i * j) * r := by
      rw [← mul_assoc, a1, neg_mul, mul_assoc, a2, mul_neg, neg_neg, mul_assoc]
    rw [a4, ← sub_eq_zero, sub_neg_eq_add, ← two_smul ℤ] at a3
    rcases H.nzd _ _ (H.tf 2 _ two_ne_zero a3) with h | h
    · exact absurd h hk0
    · exact h

  haveI hfin : Module.Finite ℤ R := Module.Finite.of_injective f hf
  haveI : Module.IsTorsionFree ℤ R := by
    refine ⟨fun n hn => fun a b hab => ?_⟩
    have hn0 : n ≠ 0 := hn.ne_zero
    have : n • (a - b) = 0 := by rw [smul_sub]; exact sub_eq_zero.mpr hab
    exact sub_eq_zero.mp (H.tf n _ hn0 this)
  have hfree : Module.Free ℤ R := Module.free_of_finite_type_torsion_free'

  have hle : Module.finrank ℤ R ≤ 4 := by
    have := LinearMap.finrank_le_finrank_of_injective hf
    rwa [Module.finrank_fin_fun] at this

  have hli : LinearIndependent ℤ e := by
    rw [Fintype.linearIndependent_iff]
    intro g hg m
    have hg' : ∀ m', ∑ n, g n * H.B (e n) (e m') = 0 := by
      intro m'
      have h1 : f (∑ n, g n • e n) = 0 := by rw [hg, _root_.map_zero]
      simp only [map_sum, map_zsmul] at h1
      have h2 := congrFun h1 m'
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hf_apply, Pi.zero_apply] using h2
    have B11 : H.B 1 1 = 2 := by rw [B_one_right, t1]
    have Bi1 : H.B i 1 = 0 := by rw [B_one_right, ti]
    have Bj1 : H.B j 1 = 0 := by rw [B_one_right, tj]
    have Bk1 : H.B (i * j) 1 = 0 := by rw [B_one_right, tk]
    have Bii : H.B i i = 2 * -u := by rw [B_self, ni]
    have Bjj : H.B j j = 2 * -v := by rw [B_self, nj]
    have Bkk : H.B (i * j) (i * j) = 2 * (u * v) := by rw [B_self, nk]
    fin_cases m
    · have := hg' 0
      simp only [Fin.sum_univ_four, e, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        B11, Bi1, Bj1, Bk1] at this
      simp only [Fin.zero_eta, Fin.isValue]
      linarith
    · have := hg' 1
      simp only [Fin.sum_univ_four, e, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        H.B_comm 1 i, Bi1, Bii, H.B_comm j i, Bij, H.B_comm (i * j) i, Bik] at this
      simp only [Fin.mk_one, Fin.isValue]
      have : (2 * u) * g 1 = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero hu)
    · have := hg' 2
      simp only [Fin.sum_univ_four, e, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        H.B_comm 1 j, Bj1, Bij, Bjj, H.B_comm (i * j) j, Bjk] at this
      simp only [Fin.reduceFinMk, Fin.isValue]
      have : (2 * v) * g 2 = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero hv)
    · have := hg' 3
      simp only [Fin.sum_univ_four, e, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        H.B_comm 1 (i * j), Bk1, Bik, Bjk, Bkk] at this
      simp only [Fin.reduceFinMk, Fin.isValue]
      have : (2 * (u * v)) * g 3 = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero (mul_ne_zero hu hv))
  have hge : 4 ≤ Module.finrank ℤ R := by
    have := hli.fintype_card_le_finrank
    rwa [Fintype.card_fin] at this
  exact ⟨hfree, hfin, le_antisymm hle hge⟩

end QH

end QuadRing

section HomSet

p2m_open_scoped "Polynomial.Bivariate Polynomial.Bivariate.Polynomial.Bivariate"

variable {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [DecidableEq k]

theorem isRationallyRepresented_neg_id (W : WeierstrassCurve F) :
    IsRationallyRepresented k W W (-(AddMonoidHom.id _)) := by
  refine ⟨C X, 1, -X - C (C W.a₁ * X + C W.a₃), 1, ∅, Set.finite_empty, fun x y h _ => ?_⟩
  have e0 : evalEvalBC k (1 : F[X][Y]) x y = 1 := by simp [evalEvalBC, Polynomial.evalEval]
  have e1 : evalEvalBC k (C X : F[X][Y]) x y = x := by simp [evalEvalBC, Polynomial.evalEval]
  have e2 : evalEvalBC k (-X - C (C W.a₁ * X + C W.a₃) : F[X][Y]) x y =
      (W.baseChange k).toAffine.negY x y := by
    simp [evalEvalBC, Polynomial.evalEval, Affine.negY, WeierstrassCurve.baseChange]
    ring
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  rw [e0, e1, e2, div_one, div_one, AddMonoidHom.neg_apply, AddMonoidHom.id_apply,
    Affine.Point.neg_some]
  exact ⟨_, rfl⟩

theorem neg_id_mem_rationalHomSet (W : WeierstrassCurve F) :
    (-(AddMonoidHom.id _) : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point) ∈
      rationalHomSet k W W :=
  Or.inr (isRationallyRepresented_neg_id k W)

variable {k}

theorem neg_mem_rationalHomSet {W₁ W₂ : WeierstrassCurve F}
    {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hα : α ∈ rationalHomSet k W₁ W₂) : -α ∈ rationalHomSet k W₁ W₂ := by
  have h := WeierstrassCurve.comp_mem_rationalHomSet k W₁ W₂ W₂ hα (neg_id_mem_rationalHomSet k W₂)
  have e : (-(AddMonoidHom.id _)).comp α = -α := by ext P; simp
  rwa [e] at h

end HomSet

section Curve

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k] [DecidableEq k] [IsAlgClosed k]
  (W : WeierstrassCurve F) [W.IsElliptic]

theorem mem_rationalHomSet_of_mem {α : AddMonoid.End (W⁄k).Point} (hα : α ∈ rationalEndSubring k W) :
    (α : (W⁄k).Point →+ (W⁄k).Point) ∈ rationalHomSet k W W := by
  let S : Subring (AddMonoid.End (W⁄k).Point) :=
    { carrier := rationalHomSet k W W
      mul_mem' := fun {a b} ha hb => WeierstrassCurve.comp_mem_rationalHomSet k W W W hb ha
      one_mem' := id_mem_rationalHomSet k W
      add_mem' := fun {a b} ha hb => WeierstrassCurve.add_mem_rationalHomSet k W W ha hb
      zero_mem' := zero_mem_rationalHomSet k W W
      neg_mem' := fun {a} ha => neg_mem_rationalHomSet ha }
  exact (Subring.closure_le (t := S)).mpr (fun x hx => hx) hα

theorem false_of_forall_smul_eq_zero {q : ℕ} (hq : (q : k) ≠ 0) (hq1 : 1 < q) {n : ℤ}
    (hqn : Int.gcd q n = 1) (h : ∀ Q : (W⁄k).Point, n • Q = 0) : False := by
  have hcard := WeierstrassCurve.card_torsion_of_isAlgClosed (K := k) W hq
  haveI : Finite (Submodule.torsionBy ℤ (W⁄k).Point (q : ℤ)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  haveI : Nontrivial (Submodule.torsionBy ℤ (W⁄k).Point (q : ℤ)) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    exact Nat.one_lt_pow two_ne_zero hq1
  obtain ⟨⟨P, hPmem⟩, hP0⟩ := exists_ne (0 : Submodule.torsionBy ℤ (W⁄k).Point (q : ℤ))
  have hqP : (q : ℤ) • P = 0 := (Submodule.mem_torsionBy_iff _ _).mp hPmem
  apply hP0
  apply Subtype.ext
  change P = 0
  have hbez := Int.gcd_eq_gcd_ab (q : ℤ) n
  rw [hqn, Nat.cast_one] at hbez
  calc P = (1 : ℤ) • P := (one_zsmul P).symm
    _ = Int.gcdA q n • ((q : ℤ) • P) + Int.gcdB q n • (n • P) := by
        rw [hbez, add_zsmul, mul_comm (q : ℤ), mul_zsmul, mul_comm n, mul_zsmul]
    _ = 0 := by rw [hqP, h P, zsmul_zero, zsmul_zero, add_zero]

theorem eq_zero_or_eq_zero_of_mul_eq_zero (a b : rationalEndSubring k W) (h : a * b = 0) :
    a = 0 ∨ b = 0 := by
  by_cases hb : b = 0
  · exact Or.inr hb
  refine Or.inl (Subtype.ext ?_)
  have hb' : (b : AddMonoid.End (W⁄k).Point) ≠ 0 := fun h0 => hb (Subtype.ext h0)
  have hsurj := surjective_of_mem_rationalHomSet k (mem_rationalHomSet_of_mem W b.2) hb'
  apply AddMonoidHom.ext
  intro Q
  obtain ⟨P, rfl⟩ := hsurj Q
  have h1 := congrArg (fun z : rationalEndSubring k W => (z : AddMonoid.End (W⁄k).Point) P) h
  first | simpa only [Subring.coe_mul, ZeroMemClass.coe_zero, AddMonoid.End.coe_mul, Function.comp_apply, AddMonoidHom.zero_apply] using h1 | (have h_1 := h1; simp only [Subring.coe_mul, ZeroMemClass.coe_zero, AddMonoid.End.coe_mul, Function.comp_apply, AddMonoidHom.zero_apply] at h_1; exact h_1) | (have h_1 := h1; simp only [Subring.coe_mul, ZeroMemClass.coe_zero, AddMonoid.End.coe_mul, Function.comp_apply, AddMonoidHom.zero_apply] at h_1 ⊢; exact h_1) | exact (h1)

theorem exists_sq_eq (a : rationalEndSubring k W) : ∃ t n : ℤ, a * a = t • a - n • (1 : rationalEndSubring k W) := by
  obtain ⟨D, -, -⟩ := WeierstrassCurve.dualIsogenyExistence_rationalEndSubring k W a.1 a.2
  refine ⟨D.trace, D.norm, Subtype.ext ?_⟩
  have h := D.charPoly
  rw [zsmul_eq_mul, zsmul_one]
  push_cast
  rw [← sub_eq_zero, ← h]
  noncomm_ring

variable (hgood : ∀ n : ℤ, n ≠ 0 → ∃ q : ℕ, 1 < q ∧ (q : k) ≠ 0 ∧ Int.gcd q n = 1)
include hgood

theorem eq_zero_of_zsmul_eq_zero (n : ℤ) (a : rationalEndSubring k W) (hn : n ≠ 0)
    (h : n • a = 0) : a = 0 := by
  rw [zsmul_eq_mul] at h
  by_contra ha
  have ha' : (a : AddMonoid.End (W⁄k).Point) ≠ 0 := fun h0 => ha (Subtype.ext h0)
  have hsurj := surjective_of_mem_rationalHomSet k (mem_rationalHomSet_of_mem W a.2) ha'
  obtain ⟨q, hq1, hq, hqn⟩ := hgood n hn
  refine false_of_forall_smul_eq_zero W hq hq1 hqn fun Q => ?_
  obtain ⟨P, rfl⟩ := hsurj Q
  have h1 := congrArg (fun z : rationalEndSubring k W => (z : AddMonoid.End (W⁄k).Point) P) h
  first | simpa only [Subring.coe_mul, SubringClass.coe_intCast, ZeroMemClass.coe_zero, AddMonoid.End.coe_mul, Function.comp_apply, AddMonoid.End.intCast_apply, AddMonoidHom.zero_apply] using h1 | (have h_1 := h1; simp only [Subring.coe_mul, SubringClass.coe_intCast, ZeroMemClass.coe_zero, AddMonoid.End.coe_mul, Function.comp_apply, AddMonoid.End.intCast_apply, AddMonoidHom.zero_apply] at h_1; exact h_1) | (have h_1 := h1; simp only [Subring.coe_mul, SubringClass.coe_intCast, ZeroMemClass.coe_zero, AddMonoid.End.coe_mul, Function.comp_apply, AddMonoid.End.intCast_apply, AddMonoidHom.zero_apply] at h_1 ⊢; exact h_1) | exact (h1)

theorem intCast_injective (n : ℤ) (h : (n : rationalEndSubring k W) = 0) : n = 0 := by
  by_contra hn
  obtain ⟨q, hq1, hq, hqn⟩ := hgood n hn
  refine false_of_forall_smul_eq_zero W hq hq1 hqn fun Q => ?_
  have h1 := congrArg (fun z : rationalEndSubring k W => (z : AddMonoid.End (W⁄k).Point) Q) h
  first | simpa only [SubringClass.coe_intCast, ZeroMemClass.coe_zero, AddMonoid.End.intCast_apply, AddMonoidHom.zero_apply] using h1 | (have h_1 := h1; simp only [SubringClass.coe_intCast, ZeroMemClass.coe_zero, AddMonoid.End.intCast_apply, AddMonoidHom.zero_apply] at h_1; exact h_1) | (have h_1 := h1; simp only [SubringClass.coe_intCast, ZeroMemClass.coe_zero, AddMonoid.End.intCast_apply, AddMonoidHom.zero_apply] at h_1 ⊢; exact h_1) | exact (h1)

theorem qh : QH (rationalEndSubring k W) where
  tf := eq_zero_of_zsmul_eq_zero W hgood
  ci := intCast_injective W hgood
  nzd := eq_zero_or_eq_zero_of_mul_eq_zero W
  quad := exists_sq_eq W

end Curve

section Descent

variable {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]

def fixFld (m : ℕ) : IntermediateField (ZMod p) k where
  carrier := {x | x ^ p ^ m = x}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [mul_pow, ha, hb]
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [add_pow_char_pow a b p m, ha, hb]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    exact zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  algebraMap_mem' c := by
    simp only [Set.mem_setOf_eq]
    rw [← map_pow, ZMod.pow_card_pow]
  inv_mem' a ha := by
    change a ^ p ^ m = a at ha
    change a⁻¹ ^ p ^ m = a⁻¹
    rw [inv_pow, ha]

theorem mem_fixFld {m : ℕ} {x : k} : x ∈ fixFld (k := k) p m ↔ x ^ p ^ m = x := Iff.rfl

theorem mem_fixFld_mul {d : ℕ} {x : k} (hx : x ∈ fixFld (k := k) p d) (n : ℕ) :
    x ∈ fixFld (k := k) p (d * n) := by
  rw [mem_fixFld] at hx ⊢
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hx]

def frob (m : ℕ) : k →ₐ[fixFld (k := k) p m] k where
  toFun x := x ^ p ^ m
  map_one' := one_pow _
  map_mul' x y := mul_pow x y _
  map_zero' := zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  map_add' x y := add_pow_char_pow x y p m
  commutes' c := c.2

theorem frob_apply (m : ℕ) (x : k) : frob (k := k) p m x = x ^ p ^ m := rfl

theorem exists_fintype_card_fixFld [IsAlgClosed k] {m : ℕ} (hm : m ≠ 0) :
    ∃ inst : Fintype (fixFld (k := k) p m), @Fintype.card _ inst = p ^ m := by
  have h1 : 1 < p := (Fact.out : p.Prime).one_lt
  set f : k[X] := X ^ p ^ m - X with hf
  have hf0 : f ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero k hm h1
  have hset : ((fixFld (k := k) p m : IntermediateField (ZMod p) k) : Set k) = f.rootSet k := by
    ext x
    rw [SetLike.mem_coe, mem_fixFld, Polynomial.mem_rootSet_of_ne hf0]
    simp [hf, sub_eq_zero]
  have hcard : Fintype.card (f.rootSet k) = p ^ m := by
    rw [Polynomial.card_rootSet_eq_natDegree (galois_poly_separable p _ (dvd_pow_self p hm))
      (IsAlgClosed.splits _), FiniteField.X_pow_card_pow_sub_X_natDegree_eq k hm h1]
  let e : (fixFld (k := k) p m) ≃ f.rootSet k := Equiv.setCongr hset
  exact ⟨Fintype.ofEquiv _ e.symm, by rw [Fintype.ofEquiv_card, hcard]⟩

omit [CharP k p] in

theorem exists_some_of_eq {W' : Affine k} [DecidableEq k] {Q : W'.Point} {x₁ y₁ : k}
    {h₁ : W'.Nonsingular x₁ y₁} (hQ : Q = .some x₁ y₁ h₁) {x₂ y₂ : k} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    ∃ h₂, Q = .some x₂ y₂ h₂ := by
  subst hx hy; exact ⟨h₁, hQ⟩

variable (X : WeierstrassCurve k)

def model (K : IntermediateField (ZMod p) k)
    (hK : ({X.a₁, X.a₂, X.a₃, X.a₄, X.a₆} : Set k) ⊆ (K : Set k)) : WeierstrassCurve K :=
  ⟨⟨X.a₁, hK (by simp)⟩, ⟨X.a₂, hK (by simp)⟩, ⟨X.a₃, hK (by simp)⟩, ⟨X.a₄, hK (by simp)⟩,
    ⟨X.a₆, hK (by simp)⟩⟩

omit [CharP k p] in

theorem model_baseChange (K : IntermediateField (ZMod p) k)
    (hK : ({X.a₁, X.a₂, X.a₃, X.a₄, X.a₆} : Set k) ⊆ (K : Set k)) :
    (model p X K hK).baseChange k = X := rfl

omit [CharP k p] in
theorem isElliptic_model [X.IsElliptic] (K : IntermediateField (ZMod p) k)
    (hK : ({X.a₁, X.a₂, X.a₃, X.a₄, X.a₆} : Set k) ⊆ (K : Set k)) : (model p X K hK).IsElliptic := by
  have hΔ : algebraMap K k (model p X K hK).Δ = X.Δ := ((model p X K hK).map_Δ (algebraMap K k)).symm
  refine ⟨isUnit_iff_ne_zero.mpr fun h0 => ?_⟩
  have hX : X.Δ ≠ 0 := (inferInstance : X.IsElliptic).isUnit.ne_zero
  exact hX (by rw [← hΔ, h0, _root_.map_zero])

omit [CharP k p] in

theorem mem_rationalHomSet_of_mem_model [DecidableEq k] {K : IntermediateField (ZMod p) k}
    (hK : ({X.a₁, X.a₂, X.a₃, X.a₄, X.a₆} : Set k) ⊆ (K : Set k))
    {α : (X⁄k).Point →+ (X⁄k).Point}
    (hα : α ∈ rationalHomSet k (model p X K hK) (model p X K hK)) : α ∈ rationalHomSet k X X := by
  rcases hα with h0 | ⟨nX, dX, nY, dY, B, hB, h⟩
  · exact Or.inl h0
  have hev : ∀ (q : K[X][Y]) (x y : k),
      evalEvalBC k (F := k) (q.map (mapRingHom (algebraMap K k))) x y = evalEvalBC k q x y := by
    intro q x y
    simp only [evalEvalBC, Polynomial.map_map, Algebra.algebraMap_self, Polynomial.mapRingHom_id,
      RingHom.id_comp]
  refine Or.inr ⟨nX.map (mapRingHom (algebraMap K k)), dX.map (mapRingHom (algebraMap K k)),
    nY.map (mapRingHom (algebraMap K k)), dY.map (mapRingHom (algebraMap K k)), B, hB,
    fun x y hxy hx => ?_⟩
  simp only [hev]
  exact h x y hxy hx

omit [CharP k p] in

theorem iterate_map_some [DecidableEq k] {K : IntermediateField (ZMod p) k}
    (hK : ({X.a₁, X.a₂, X.a₃, X.a₄, X.a₆} : Set k) ⊆ (K : Set k)) (d : ℕ)
    (σ : k →ₐ[K] k) (hσ : ∀ x, σ x = x ^ p ^ d) (n : ℕ) :
    ∀ (x y : k) (h : ((model p X K hK)⁄k).Nonsingular x y),
      ∃ h', (Point.map (W' := model p X K hK) σ)^[n] (.some x y h)
        = .some (x ^ p ^ (d * n)) (y ^ p ^ (d * n)) h' := by
  induction n with
  | zero =>
    intro x y h
    exact exists_some_of_eq rfl (by simp) (by simp)
  | succ n ih =>
    intro x y h
    obtain ⟨h', e⟩ := ih x y h
    have e2 : (Point.map (W' := model p X K hK) σ)^[n + 1] (.some x y h)
        = Point.map (W' := model p X K hK) σ (.some _ _ h') := by
      rw [Function.iterate_succ_apply', e]
    rw [Point.map_some] at e2
    exact exists_some_of_eq e2 (by rw [hσ, ← pow_mul, ← pow_add, Nat.mul_succ])
      (by rw [hσ, ← pow_mul, ← pow_add, Nat.mul_succ])

theorem exists_anticommuting_pair [DecidableEq k] [IsAlgClosed k] [Algebra.IsAlgebraic (ZMod p) k]
    [X.IsElliptic] (hss : ∀ P : X.toAffine.Point, p • P = 0 → P = 0) :
    ∃ i ∈ rationalHomSet k X X, ∃ j ∈ rationalHomSet k X X, ∃ u v : ℤ, u ≠ 0 ∧ v ≠ 0 ∧
      (∀ P, i (i P) = u • P) ∧ (∀ P, j (j P) = v • P) ∧ (∀ P, i (j P) = -(j (i P))) := by

  set S : Set k := {X.a₁, X.a₂, X.a₃, X.a₄, X.a₆} with hS
  let K₀ : IntermediateField (ZMod p) k := IntermediateField.adjoin (ZMod p) S
  haveI : FiniteDimensional (ZMod p) K₀ := IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := ZMod p) x).isIntegral)
  haveI : Finite K₀ := Module.finite_of_finite (ZMod p)
  letI : Fintype K₀ := Fintype.ofFinite K₀
  haveI : CharP K₀ p := charP_of_injective_algebraMap (algebraMap (ZMod p) K₀).injective p
  obtain ⟨d, -, hd⟩ := FiniteField.card K₀ p
  have hSK₀ : S ⊆ (K₀ : Set k) := IntermediateField.subset_adjoin (ZMod p) S
  have hK₁ : S ⊆ (fixFld (k := k) p d : Set k) := by
    intro c hc
    have hc' : c ∈ K₀ := hSK₀ hc
    change c ∈ fixFld (k := k) p d
    rw [mem_fixFld]
    have h1 := FiniteField.pow_card (⟨c, hc'⟩ : K₀)
    rw [hd] at h1
    simpa using congrArg Subtype.val h1

  have hd0 : (d : ℕ) ≠ 0 := d.pos.ne'
  obtain ⟨instK₁, hcard₁⟩ := exists_fintype_card_fixFld (k := k) p hd0
  haveI : Algebra.IsAlgebraic (fixFld (k := k) p d) k :=
    Algebra.IsAlgebraic.tower_top (K := ZMod p) _
  haveI : CharP (fixFld (k := k) p d) p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) _).injective p
  haveI := isElliptic_model p X (fixFld p d) hK₁
  obtain ⟨n, hn, a, ha⟩ :=
    WeierstrassCurve.exists_iterate_frobenius_eq_smul_of_forall_nsmul_char_eq_zero
      (F := fixFld (k := k) p d) k p (model p X _ hK₁) (frob p d)
      (fun x => by rw [hcard₁]; rfl) (fun P hP => hss P hP)

  have hK : S ⊆ (fixFld (k := k) p (d * n) : Set k) := fun c hc => mem_fixFld_mul p (hK₁ hc) n
  have hdn0 : (d : ℕ) * n ≠ 0 := Nat.mul_ne_zero hd0 hn.ne'
  obtain ⟨instK, hcard⟩ := exists_fintype_card_fixFld (k := k) p hdn0
  haveI : Algebra.IsAlgebraic (fixFld (k := k) p (d * n)) k :=
    Algebra.IsAlgebraic.tower_top (K := ZMod p) _
  haveI := isElliptic_model p X (fixFld p (d * n)) hK
  have hσ : ∀ x : k, frob (k := k) p (d * n) x = x ^ Fintype.card (fixFld (k := k) p (d * n)) :=
    fun x => by rw [hcard]; rfl
  have haσ : ∀ P : ((model p X _ hK)⁄k).Point,
      Point.map (W' := model p X _ hK) (frob p (d * n)) P = a • P := by
    rintro (_ | @⟨x, y, h⟩)
    · rw [← Point.zero_def, _root_.map_zero, smul_zero]
    · obtain ⟨h1, e1⟩ := iterate_map_some p X hK₁ d (frob p d) (frob_apply p d) n x y h
      have hP := ha (.some x y h)
      rw [e1] at hP
      rw [Point.map_some]
      exact hP
  obtain ⟨i, hi, j, hj, u, v, hu, hv, hii, hjj, hij⟩ :=
    WeierstrassCurve.exists_anticommuting_pair_mem_rationalHomSet_of_frobenius_eq_smul
      (F := fixFld (k := k) p (d * n)) k (model p X _ hK) (frob p (d * n)) hσ a haσ
  exact ⟨i, mem_rationalHomSet_of_mem_model p X hK hi, j, mem_rationalHomSet_of_mem_model p X hK hj,
    u, v, hu, hv, hii, hjj, hij⟩

end Descent

section Main

theorem hgood_char (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] :
    ∀ n : ℤ, n ≠ 0 → ∃ q : ℕ, 1 < q ∧ (q : k) ≠ 0 ∧ Int.gcd q n = 1 := by
  intro n hn
  obtain ⟨q, hle, hq⟩ := Nat.exists_infinite_primes (n.natAbs + p + 1)
  refine ⟨q, hq.one_lt, ?_, ?_⟩
  · rw [Ne, CharP.cast_eq_zero_iff k p q]
    intro hdvd
    have := (Nat.prime_dvd_prime_iff_eq Fact.out hq).mp hdvd
    omega
  · rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
    refine (Nat.Prime.coprime_iff_not_dvd hq).mpr fun h => ?_
    have := Nat.le_of_dvd (Int.natAbs_pos.mpr hn) h
    omega

variable {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]
  (p : ℕ) [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k] [Algebra.IsAlgebraic (ZMod p) k]
  (X : WeierstrassCurve k) [X.IsElliptic]

theorem main (hss : ∀ P : X.toAffine.Point, p • P = 0 → P = 0) :
    Module.Free ℤ ↥(WeierstrassCurve.rationalEndSubring k X) ∧
      Module.Finite ℤ ↥(WeierstrassCurve.rationalEndSubring k X) ∧
      Module.finrank ℤ ↥(WeierstrassCurve.rationalEndSubring k X) = 4 := by
  obtain ⟨i, hi, j, hj, u, v, hu, hv, hii, hjj, hij⟩ := exists_anticommuting_pair p X hss
  have H : QH (rationalEndSubring k X) := qh X (hgood_char k p)
  let I : rationalEndSubring k X := ⟨i, Subring.subset_closure hi⟩
  let J : rationalEndSubring k X := ⟨j, Subring.subset_closure hj⟩
  have hI : I * I = ((u : ℤ) : rationalEndSubring k X) := by
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro P
    simp only [I, Subring.coe_mul, SubringClass.coe_intCast]
    exact hii P
  have hJ : J * J = ((v : ℤ) : rationalEndSubring k X) := by
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro P
    simp only [J, Subring.coe_mul, SubringClass.coe_intCast]
    exact hjj P
  have hIJ : I * J = -(J * I) := by
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro P
    simp only [I, J, Subring.coe_mul, NegMemClass.coe_neg]
    exact hij P
  exact H.free_and_finite_and_finrank_eq_four hu hv hI hJ hIJ

end Main

end WeierstrassCurve.SupersingularEndRank

open scoped Quaternion TensorProduct in

theorem solution
    {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]
    (p : ℕ) [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k] [Algebra.IsAlgebraic (ZMod p) k]
    (X : WeierstrassCurve k) [X.IsElliptic]
    (hss : ∀ P : X.toAffine.Point, p • P = 0 → P = 0) :
    Module.Free ℤ ↥(WeierstrassCurve.rationalEndSubring k X) ∧ Module.Finite ℤ ↥(WeierstrassCurve.rationalEndSubring k X) ∧
      Module.finrank ℤ ↥(WeierstrassCurve.rationalEndSubring k X) = 4 :=
  WeierstrassCurve.SupersingularEndRank.main p X hss

end S_WeierstrassCurve_free_and_finrank_rationalEndSubring_eq_four
end P2MW
export P2MW.S_WeierstrassCurve_free_and_finrank_rationalEndSubring_eq_four (solution)
