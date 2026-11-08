-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalField_reciprocal_integral_of_noPole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:50:16.759669+00:00
-- url     : https://prove2.me/submissions/2ad0ab82-b331-4fac-a14e-200ccd313b10

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNumerator
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPowerPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalFieldIntegral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4Ratio_reciprocal_integral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalReciprocalClearedRepresentative_compact_germ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4PowerHolomorphic_ne_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldLocalOrder_value
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldToLocal_representative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalField_j_power_clear_interior
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedRestriction_representative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphicFractionToMeromorphicGerm_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalReciprocalNumerator_germ_identity
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalCriterionDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => LPSOriginalHolomorphicRing
local notation "H" => LPSOriginalHolomorphicFractionField
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
local notation "C" => CuspOrbits
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalCriterionDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalCriterionDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalCriterionDictionary004
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (f : K)
    (hi : ∀ x : Q, lpsOriginalFilledJ N (Sum.inl x) ≠ 0 →
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) f)
    (hc : ∀ c : C, 0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inr c) f) :
    (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).IsIntegralElem f := by
  obtain ⟨F,hF⟩ := (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict_surjective
    (lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN f)
  obtain ⟨k,hk⟩ := lpsOriginalField_j_power_clear_interior N hpos hN f hi
  have hcF : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ c : C, 0 ≤ meromorphicOrderAt
        (F.val ∘ (chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N)).symm)
        (chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N) (Sum.inr c)) := by
    let := lpsOriginalFilledTopology N
    let := lpsOriginalFilledChartedSpace N hN
    intro c
    have ho := hc c
    rw [lpsOriginalFieldLocalOrder_value,
      lpsOriginalFieldToLocal_representative N hN hpos (Sum.inr c) f F hF] at ho
    exact ho
  let G := lpsOriginalReciprocalClearedRepresentative N hN F.val F.property k
  have hG := lpsOriginalReciprocalClearedRepresentative_compact_germ
    N hpos hN f F hF k
  have hiG : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ x : Q, 0 ≤ meromorphicOrderAt
        (G.val ∘ (chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N)).symm)
        (chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N) (Sum.inl x)) := by
    let := lpsOriginalFilledTopology N
    let := lpsOriginalFilledChartedSpace N hN
    intro x
    have ho := hk x
    rw [lpsOriginalFieldLocalOrder_value,
      lpsOriginalFieldToLocal_representative N hN hpos (Sum.inl x)
        ((algebraMap P K Polynomial.X)^k*f) G hG] at ho
    exact ho
  let A := lpsOriginalReciprocalNumeratorModularForm N hN F.val F.property hcF k hiG
  have hnum := lpsOriginalReciprocalNumerator_germ_identity
    N hN F.val F.property hcF k hiG
  have hres := congrArg Subtype.val
    (lpsOriginalGeneratedRestriction_representative N hpos hN f F hF)
  change lpsOriginalHolomorphicFractionToMeromorphicGerm f.val =
    (lpsOriginalFilledMeromorphicRestriction N hN F.val F.property).val at hres
  have hB : algebraMap R H (lpsOriginalE4PowerHolomorphic k) ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R H).ne
      (lpsOriginalE4PowerHolomorphic_ne_zero k)
  apply lpsOriginalE4Ratio_reciprocal_integral N hpos k A f
  apply (eq_div_iff hB).mpr
  apply lpsOriginalHolomorphicFractionToMeromorphicGerm_injective
  rw [map_mul, lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic,
    lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic]
  change lpsOriginalHolomorphicFractionToMeromorphicGerm f.val * _ = _
  rw [hres]
  exact (mul_comm _ _).trans hnum.symm
end QEC.Coding.TannerLiftedProduct
