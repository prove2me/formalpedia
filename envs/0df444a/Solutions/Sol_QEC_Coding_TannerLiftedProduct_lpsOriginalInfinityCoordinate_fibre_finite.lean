-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityCoordinate_fibre_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:12:38.297224+00:00
-- url     : https://prove2.me/submissions/18ce2a02-d662-4702-bd4d-3ab6f7fe58cf

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityRegularPoints
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFiniteInteriorFibres
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityFiniteFibres
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityCoordinate_interior
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityRegular_interior_nonzero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFibre_finite


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
theorem _root_.solution (α : ℂ) :
    {x : S | lpsOriginalInfinityCoordinate N hpos hN x = α}.Finite := by
  let U : Set (LPSOriginalFilledCurve N) :=
    Sum.inl '' {y : Q | lpsOriginalFilledJ N (Sum.inl y) = α⁻¹} ∪
      Sum.inr '' (Set.univ : Set C)
  have hu : U.Finite :=
    ((lpsOriginalJFibre_finite N hpos hN α⁻¹).image Sum.inl).union
      ((Set.toFinite (Set.univ : Set C)).image Sum.inr)
  apply (hu.preimage Subtype.val_injective.injOn).subset
  rintro ⟨x,hx⟩ hα
  cases x with
  | inl y =>
    have hy := lpsOriginalInfinityRegular_interior_nonzero N hpos hN y hx
    have hv : (lpsOriginalFilledJ N (Sum.inl y))⁻¹ = α :=
      (lpsOriginalInfinityCoordinate_interior N hpos hN y hy).symm.trans hα
    exact Or.inl ⟨y,by change lpsOriginalFilledJ N (Sum.inl y) = α⁻¹; rw [←hv,inv_inv],rfl⟩
  | inr c => exact Or.inr ⟨c,Set.mem_univ _,rfl⟩
end QEC.Coding.TannerLiftedProduct
