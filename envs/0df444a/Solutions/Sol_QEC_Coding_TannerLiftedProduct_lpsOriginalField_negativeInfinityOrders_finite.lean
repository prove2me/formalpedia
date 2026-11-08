-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalField_negativeInfinityOrders_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:08:00.877206+00:00
-- url     : https://prove2.me/submissions/599705e0-c686-4fa4-b71c-4614e658f2df

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityRegularPoints
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFiniteInteriorFibres
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityFiniteFibres
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalField_negativeInteriorOrders_finite


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
    {x : S | lpsOriginalFieldLocalOrder N hN hpos x.val f < 0}.Finite := by
  let U : Set (LPSOriginalFilledCurve N) :=
    Sum.inl '' {y : Q | lpsOriginalFieldLocalOrder N hN hpos (Sum.inl y) f < 0} ∪
      Sum.inr '' (Set.univ : Set C)
  have hu : U.Finite :=
    ((lpsOriginalField_negativeInteriorOrders_finite N hpos hN f).image Sum.inl).union
      ((Set.toFinite (Set.univ : Set C)).image Sum.inr)
  apply (hu.preimage Subtype.val_injective.injOn).subset
  rintro ⟨x,hx⟩ hbad
  cases x with
  | inl y => exact Or.inl ⟨y,hbad,rfl⟩
  | inr c => exact Or.inr ⟨c,Set.mem_univ _,rfl⟩
end QEC.Coding.TannerLiftedProduct
