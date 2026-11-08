-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalField_reciprocal_integral_iff_regularPoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:08:11.106208+00:00
-- url     : https://prove2.me/submissions/04426a84-ea30-4bb4-af26-6f1c1f4adb52

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityRegularPoints
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFiniteInteriorFibres
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityFiniteFibres
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldJ_inverse_cusp_order_nonnegative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldJ_inverse_interior_order_nonnegative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalField_reciprocal_integral_iff_noPole
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityRegular_interior_nonzero


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular BigOperators
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityFiniteFibresDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityFiniteFibresDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityFiniteFibresDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityFiniteFibresDictionary004
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
local notation "C" => CuspOrbits
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
local notation "S" => lpsOriginalInfinityRegularPoints N hpos hN
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (f : K) :
    (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).IsIntegralElem f ↔
      ∀ x : S, 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x.val f := by
  rw [lpsOriginalField_reciprocal_integral_iff_noPole N hpos hN f]
  constructor
  · rintro ⟨hi,hc⟩ ⟨x,hx⟩
    cases x with
    | inl y => exact hi y (lpsOriginalInfinityRegular_interior_nonzero N hpos hN y hx)
    | inr c => exact hc c
  · intro h
    exact ⟨fun y hy => h ⟨Sum.inl y,
      lpsOriginalFieldJ_inverse_interior_order_nonnegative N hpos hN y hy⟩,
      fun c => h ⟨Sum.inr c,lpsOriginalFieldJ_inverse_cusp_order_nonnegative N hpos hN c⟩⟩
end QEC.Coding.TannerLiftedProduct
