-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalField_reciprocal_integral_iff_noPole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:05:01.329017+00:00
-- url     : https://prove2.me/submissions/ed71ede8-44aa-4b8a-be1a-cc7d00a2a4e1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNumerator
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPowerPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalFieldIntegral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalField_reciprocal_integral_of_noPole
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldJ_inverse_interior_order_nonnegative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldJ_inverse_cusp_order_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_nonnegative_of_integral_map


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
theorem _root_.solution (f : K) :
    (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).IsIntegralElem f ↔
      (∀ x : Q, lpsOriginalFilledJ N (Sum.inl x) ≠ 0 →
        0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) f) ∧
      (∀ c : C, 0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inr c) f) := by
  constructor
  · intro hf
    have hp (x : LPSOriginalFilledCurve N)
        (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x
          (algebraMap P K Polynomial.X)⁻¹) :
        0 ≤ lpsOriginalFieldLocalOrder N hN hpos x f :=
      nonnegative_of_integral_map (lpsOriginalFieldLocalOrder N hN hpos x)
        (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos)
        (lpsOriginalReciprocalFieldPolynomialMap_order_nonnegative N hpos hN x hj) hf
    exact ⟨fun x hx => hp (Sum.inl x)
      (lpsOriginalFieldJ_inverse_interior_order_nonnegative N hpos hN x hx),
      fun c => hp (Sum.inr c)
        (lpsOriginalFieldJ_inverse_cusp_order_nonnegative N hpos hN c)⟩
  · rintro ⟨hi,hc⟩
    exact lpsOriginalField_reciprocal_integral_of_noPole N hpos hN f hi hc
end QEC.Coding.TannerLiftedProduct
