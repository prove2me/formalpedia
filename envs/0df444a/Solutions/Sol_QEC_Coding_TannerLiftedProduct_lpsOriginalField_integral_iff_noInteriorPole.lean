-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalField_integral_iff_noInteriorPole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:28:25.078735+00:00
-- url     : https://prove2.me/submissions/c077504f-f721-4c93-954f-8e4069b02b0d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizedIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalMeromorphicOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFieldIntegral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldJ_interior_order_nonnegative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedRestriction_representative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldLocalOrder_integral_nonnegative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldLocalOrder_value
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldToLocal_representative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledNoInteriorPole_integral


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFieldIntegralDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "E" => lpsOriginalFilledMeromorphicRestrictionSubfield N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFieldIntegralDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFieldIntegralDictionary003
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (f : K) :
    IsIntegral P f ↔ ∀ x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ,
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) f := by
  constructor
  · intro hi x
    exact lpsOriginalFieldLocalOrder_integral_nonnegative N hN hpos (Sum.inl x)
      (lpsOriginalFieldJ_interior_order_nonnegative N hpos hN x) ⟨f,hi⟩
  · intro hno
    obtain ⟨F,hF⟩ := (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict_surjective
      (lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN f)
    have hn : letI := lpsOriginalFilledTopology N
        letI := lpsOriginalFilledChartedSpace N hN
        ∀ x : MulAction.orbitRel.Quotient
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ,
        0 ≤ meromorphicOrderAt (F.val ∘ (chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N)).symm)
          (chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N) (Sum.inl x)) := by
      let := lpsOriginalFilledTopology N
      let := lpsOriginalFilledChartedSpace N hN
      intro x
      have ho := hno x
      rw [lpsOriginalFieldLocalOrder_value,
        lpsOriginalFieldToLocal_representative N hN hpos (Sum.inl x) f F hF] at ho
      exact ho
    have hi := lpsOriginalFilledNoInteriorPole_integral N hN F.val F.property hn
    apply (isIntegral_algHom_iff (lpsOriginalGeneratedRestrictionPolynomialAlgEquiv N hpos hN).toAlgHom
      (lpsOriginalGeneratedRestrictionPolynomialAlgEquiv N hpos hN).injective).mp
    change IsIntegral P (lpsOriginalGeneratedRestrictionPolynomialAlgEquiv N hpos hN f)
    rwa [lpsOriginalGeneratedRestriction_representative N hpos hN f F hF]
end QEC.Coding.TannerLiftedProduct
